// Predictive Input Buffer v1.5 - prediccion por trayectoria (Windows / Android)
// Etapas (ticks a 240 Hz): 2/2 -> 4/4 -> 8/8 -> 16/8 -> 32/16 -> 64/32 -> OFF  (all / wave)
//
//  ARO/ORBE : al pulsar se simula la trayectoria; si va a tocar un aro, el press se aplaza
//             hasta el contacto. Si ya lo soltaste, se envia press + release en el contacto.
//  ATERRIZAJE (cubo / bola / spider): si pulsas en el aire y sueltas antes de aterrizar,
//             el salto se ejecuta al tocar el suelo si caes dentro de la ventana `all`.
//  WAVE     : cada cambio de direccion se simula; si retrasarlo 1..wave ticks evita un
//             choque por completo, se retrasa. Las entradas conservan su orden.
#include <Geode/Geode.hpp>
#include <Geode/modify/GJBaseGameLayer.hpp>
#include <Geode/modify/PlayLayer.hpp>
#include <algorithm>
#include <cmath>
#include <vector>
#include <unordered_set>

using namespace geode::prelude;

struct Stage { int all; int wave; const char* label; };
static constexpr Stage STAGES[] = {
	{2, 2, "Buf 2/2"},
	{4, 4, "Buf 4/4"},
	{8, 8, "Buf 8/8"},
	{16, 8, "Buf 16/8"},
	{32, 16, "Buf 32/16"},
	{64, 32, "Buf 64/32"},
	{0, 0, "Buf OFF"},
};
static constexpr int STAGE_COUNT = sizeof(STAGES) / sizeof(STAGES[0]);
static constexpr int OFF_STAGE = STAGE_COUNT - 1;

static int g_stage = 0;
static int g_tick = 0;
static std::vector<RingObject*> g_rings;
static std::vector<GameObject*> g_hazards;
static std::vector<GameObject*> g_solids;

struct WaveCmd { bool down; int tick; };

struct PlayerBuf {
	// press recordado (aros / aterrizaje)
	bool pending = false;     // hay un press recordado
	bool deferred = false;    // el press aun NO se envio al juego
	bool released = false;    // el jugador ya solto desde ese press
	bool landPending = false; // esperar aterrizaje
	int pendTick = 0;
	// cola de comandos retrasados (se conserva el orden)
	std::vector<WaveCmd> queue;
	bool lastDown = false;
	// cinematica medida
	bool haveLast = false;
	float lastX = 0.f, lastY = 0.f;
	float vx = 0.f, vy = 0.f, ay = 0.f;
};
static PlayerBuf g_p[2];
static std::unordered_set<RingObject*> g_touched[2];

static constexpr float RING_RADIUS = 30.f;

static void resetBuffer() {
	g_tick = 0;
	g_p[0] = PlayerBuf{};
	g_p[1] = PlayerBuf{};
	g_touched[0].clear();
	g_touched[1].clear();
}

static int allLimit()  { return STAGES[g_stage].all; }
static int waveLimit() { return STAGES[g_stage].wave; }

static bool optRing()  { return Mod::get()->getSettingValue<bool>("ring-buffer"); }
static bool optLand()  { return Mod::get()->getSettingValue<bool>("land-buffer"); }
static bool optWave()  { return Mod::get()->getSettingValue<bool>("wave-buffer"); }
static bool optLog()   { return Mod::get()->getSettingValue<bool>("log-saves"); }

// cubo, bola y spider (modos donde saltar necesita estar en el suelo)
static bool groundMode(PlayerObject* pl) {
	return !(pl->m_isShip || pl->m_isBird || pl->m_isDart || pl->m_isRobot || pl->m_isSwing);
}

// ---------------------------------------------------------------- aros
static bool ringActivated(RingObject* r, bool p1) {
	return g_touched[p1 ? 0 : 1].count(r) > 0;
}

static bool predictRingAhead(PlayerObject* pl, const PlayerBuf& st, bool p1, int limit) {
	if (!pl || !st.haveLast) return false;
	float x = pl->getPositionX();
	float y = pl->getPositionY();
	float reach = std::fabs(st.vx) * limit + RING_RADIUS + 20.f;

	for (auto* ring : g_rings) {
		if (!ring || ringActivated(ring, p1)) continue;
		float rx = ring->getPositionX();
		float ry = ring->getPositionY();
		if (std::fabs(rx - x) > reach) continue;
		if (std::fabs(x - rx) < RING_RADIUS && std::fabs(y - ry) < RING_RADIUS) return false;
		for (int k = 1; k <= limit; k++) {
			float px = x + st.vx * k;
			float py = y + st.vy * k + st.ay * (k * (k + 1) / 2.f);
			if (std::fabs(px - rx) < RING_RADIUS && std::fabs(py - ry) < RING_RADIUS) return true;
		}
	}
	return false;
}

// ---------------------------------------------------------------- wave
static bool boxHit(const CCRect& r, float x, float y, float h) {
	return !(x + h < r.origin.x || x - h > r.origin.x + r.size.width ||
	         y + h < r.origin.y || y - h > r.origin.y + r.size.height);
}

// Elige cuantos ticks retrasar la entrada de wave (0 = pasa al instante).
static int chooseWaveDelay(PlayerObject* pl, const PlayerBuf& st, bool down) {
	int limit = waveLimit();
	if (!pl || !st.haveLast || limit <= 0) return 0;
	float vx = std::fabs(st.vx);
	if (vx < 0.01f) return 0;

	const int H = (int)Mod::get()->getSettingValue<int64_t>("wave-horizon");
	const float pad = (float)Mod::get()->getSettingValue<double>("wave-padding");
	const bool useSolids = Mod::get()->getSettingValue<bool>("wave-solids");

	float x0 = pl->getPositionX();
	float y0 = pl->getPositionY();

	float half = 5.f * std::fabs(pl->getScaleX());
	{
		auto pr = pl->getObjectRect();
		if (pr.size.width > 1.f && pr.size.width < 30.f) half = pr.size.width / 2.f;
	}
	half += pad;

	float slope = 1.f;
	if (std::fabs(st.vy) > 0.01f) slope = std::fabs(st.vy) / vx;
	if (slope < 0.5f || slope > 3.f) slope = 1.f;

	float flip = pl->m_isUpsideDown ? -1.f : 1.f;
	float dirNew = (down ? 1.f : -1.f) * flip;
	float dirOld = -dirNew;

	std::vector<CCRect> near;
	float xMax = x0 + vx * H + 80.f;
	auto collect = [&](std::vector<GameObject*>& list) {
		for (auto* o : list) {
			if (!o) continue;
			float ox = o->getPositionX();
			if (ox < x0 - 80.f || ox > xMax) continue;
			CCRect r = o->getObjectRect();
			r.origin.x += 1.f; r.origin.y += 1.f;
			r.size.width -= 2.f; r.size.height -= 2.f;
			near.push_back(r);
		}
	};
	collect(g_hazards);
	if (useSolids) collect(g_solids);
	if (near.empty()) return 0;

	auto ttc = [&](int d) {
		float x = x0, y = y0;
		for (int k = 1; k <= H; k++) {
			float dir = (k <= d) ? dirOld : dirNew;
			x += vx;
			y += dir * slope * vx;
			for (auto& r : near) {
				if (boxHit(r, x, y, half)) return k;
			}
		}
		return H + 1;
	};

	if (ttc(0) > H) return 0;
	for (int d = 1; d <= limit; d++) {
		if (ttc(d) > H) return d;
	}
	return 0;
}

// ---------------------------------------------------------------- hooks
class $modify(BufBaseGameLayer, GJBaseGameLayer) {
	// envia un press ahora; si el jugador ya habia soltado, encola el release 1 tick despues
	void firePress(int i, bool alsoRelease) {
		auto& st = g_p[i];
		GJBaseGameLayer::handleButton(true, 1, i == 0);
		if (alsoRelease) st.queue.push_back({false, g_tick + 1});
	}

	void clearPending(PlayerBuf& st) {
		st.pending = false;
		st.deferred = false;
		st.landPending = false;
		st.released = false;
	}

	void handleButton(bool down, int button, bool isPlayer1) {
		if (g_stage == OFF_STAGE || button != 1) {
			return GJBaseGameLayer::handleButton(down, button, isPlayer1);
		}
		int i = isPlayer1 ? 0 : 1;
		auto& st = g_p[i];
		auto* pl = isPlayer1 ? m_player1 : m_player2;
		if (!pl) return GJBaseGameLayer::handleButton(down, button, isPlayer1);

		// entradas retenidas: esta va detras (no se altera el orden)
		if (!st.queue.empty()) {
			int t = std::max(g_tick, st.queue.back().tick + 1);
			st.queue.push_back({down, t});
			st.lastDown = down;
			return;
		}

		// ---- WAVE
		if (pl->m_isDart && optWave()) {
			clearPending(st);
			bool redundant = (down == st.lastDown);
			st.lastDown = down;
			int d = redundant ? 0 : chooseWaveDelay(pl, st, down);
			if (d > 0) {
				st.queue.push_back({down, g_tick + d});
				if (optLog()) {
					log::info("[InputBuffer] WAVE {} delayed +{} ticks ({:.2f} frames @ 60fps) [Limit: {}]",
						down ? "press" : "release", d, d / 4.f, waveLimit());
				}
				return;
			}
			return GJBaseGameLayer::handleButton(down, button, isPlayer1);
		}
		st.lastDown = down;

		bool ring = optRing();
		bool land = optLand();
		if (!ring && !land) return GJBaseGameLayer::handleButton(down, button, isPlayer1);

		// ---- PRESS
		if (down) {
			clearPending(st);
			st.pendTick = g_tick;

			if (ring && predictRingAhead(pl, st, isPlayer1, allLimit())) {
				// aro en la trayectoria: esperar al contacto
				st.pending = true;
				st.deferred = true;
				if (land && groundMode(pl) && !pl->m_isOnGround) st.landPending = true;
				return;
			}
			st.pending = true;
			if (land && groundMode(pl) && !pl->m_isOnGround) st.landPending = true;
			return GJBaseGameLayer::handleButton(true, button, isPlayer1);
		}

		// ---- RELEASE
		st.released = true;
		if (st.deferred) return; // se emitira junto con el press diferido
		GJBaseGameLayer::handleButton(false, button, isPlayer1);
	}

	void processCommands(float dt, bool isHalfTick, bool isLastTick) {
		if (!isHalfTick) g_tick++;

		if (!isHalfTick) {
			PlayerObject* players[2] = {m_player1, m_player2};
			for (int i = 0; i < 2; i++) {
				auto& st = g_p[i];
				auto* pl = players[i];

				// 1) comandos retrasados (uno por tick, en orden)
				if (!st.queue.empty() && g_tick >= st.queue.front().tick) {
					WaveCmd c = st.queue.front();
					st.queue.erase(st.queue.begin());
					GJBaseGameLayer::handleButton(c.down, 1, i == 0);
				}

				if (g_stage == OFF_STAGE || !st.pending) continue;

				// 2) expiro la ventana
				if (g_tick - st.pendTick > allLimit()) {
					if (st.deferred) firePress(i, st.released); // fallback: no se pierde el press
					clearPending(st);
					continue;
				}

				// 3) aterrizaje (cubo/bola/spider) con el boton ya soltado
				if (st.landPending && pl && pl->m_isOnGround) {
					if (st.released && !st.deferred) {
						int saved = g_tick - st.pendTick;
						firePress(i, true);
						if (optLog()) {
							log::info("[InputBuffer] LAND SAVED +{} ticks ({:.2f} frames @ 60fps) [Limit: {}]",
								saved, saved / 4.f, allLimit());
						}
					}
					clearPending(st);
				}
			}
		}

		GJBaseGameLayer::processCommands(dt, isHalfTick, isLastTick);

		if (isHalfTick) return;
		PlayerObject* players[2] = {m_player1, m_player2};
		for (int i = 0; i < 2; i++) {
			auto* pl = players[i];
			if (!pl) continue;
			auto& st = g_p[i];
			float x = pl->getPositionX();
			float y = pl->getPositionY();
			if (st.haveLast) {
				float nvx = x - st.lastX;
				float nvy = y - st.lastY;
				st.ay = nvy - st.vy;
				st.vx = nvx;
				st.vy = nvy;
			}
			st.lastX = x;
			st.lastY = y;
			st.haveLast = true;
		}
	}

	void playerTouchedRing(PlayerObject* player, RingObject* ring) {
		GJBaseGameLayer::playerTouchedRing(player, ring);
		int i = (player == m_player1) ? 0 : 1;
		g_touched[i].insert(ring);
		if (g_stage == OFF_STAGE || !optRing()) return;

		auto& st = g_p[i];
		if (!st.pending || g_tick - st.pendTick > allLimit()) return;

		int saved = g_tick - st.pendTick;
		bool wasReleased = st.released;
		clearPending(st);
		// re-dispara el press ahora que el aro toca al jugador (+ release si ya habia soltado)
		firePress(i, wasReleased);
		if (optLog()) {
			log::info("[InputBuffer] RING SAVED +{} ticks ({:.2f} frames @ 60fps) [Limit: {}]",
				saved, saved / 4.f, allLimit());
		}
	}
};

class $modify(BufPlayLayer, PlayLayer) {
	void setupHasCompleted() {
		PlayLayer::setupHasCompleted();
		resetBuffer();

		g_rings.clear();
		g_hazards.clear();
		g_solids.clear();
		if (m_objects) {
			for (auto* obj : CCArrayExt<GameObject*>(m_objects)) {
				if (!obj) continue;
				if (auto* ring = typeinfo_cast<RingObject*>(obj)) {
					g_rings.push_back(ring);
					continue;
				}
				if (obj->m_objectType == GameObjectType::Hazard) g_hazards.push_back(obj);
				else if (obj->m_objectType == GameObjectType::Solid) g_solids.push_back(obj);
			}
		}

		g_stage = Mod::get()->getSavedValue<int>("stage", 0);
		if (g_stage < 0 || g_stage >= STAGE_COUNT) g_stage = 0;

		if (!Mod::get()->getSettingValue<bool>("show-button")) return;

		auto label = CCLabelBMFont::create(STAGES[g_stage].label, "bigFont.fnt");
		label->setScale(0.45f);
		label->setOpacity(160);
		auto btn = CCMenuItemExt::createSpriteExtra(label, [label](CCObject*) {
			g_stage = (g_stage + 1) % STAGE_COUNT;
			Mod::get()->setSavedValue<int>("stage", g_stage);
			label->setString(STAGES[g_stage].label);
			log::info("[InputBuffer] Stage -> {} ({} all / {} wave)",
				STAGES[g_stage].label, allLimit(), waveLimit());
		});
		auto menu = CCMenu::create();
		menu->setPosition({0, 0});
		btn->setPosition({55.f, 18.f});
		menu->addChild(btn);
		this->addChild(menu, 200);
	}

	void resetLevel() {
		PlayLayer::resetLevel();
		resetBuffer();
	}

	void onQuit() {
		resetBuffer();
		g_rings.clear();
		g_hazards.clear();
		g_solids.clear();
		PlayLayer::onQuit();
	}
};

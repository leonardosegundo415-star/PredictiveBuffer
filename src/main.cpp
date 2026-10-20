// Predictive Input Buffer v1.3 - prediccion por trayectoria (Windows / Android)
// Etapas (ticks a 240 Hz): 2/2 -> 4/4 -> 8/8 -> 16/8 -> OFF  (all / wave)
//
//  ARO/ORBE : al pulsar se simula la trayectoria; si va a tocar un aro, el press se aplaza
//             hasta el contacto. Si no, pasa al instante (zero-lag).
//  WAVE     : cada cambio de direccion (press o release) se simula hacia adelante.
//             Si con retraso 0 la wave choca con un hazard, se prueba retrasar la
//             entrada 1..wave ticks y se elige el retraso que mas tarda en chocar
//             (o que evita el choque). Si ya es seguro, pasa al instante.
#include <Geode/Geode.hpp>
#include <Geode/modify/GJBaseGameLayer.hpp>
#include <Geode/modify/PlayLayer.hpp>
#include <cmath>
#include <vector>

using namespace geode::prelude;

struct Stage { int all; int wave; const char* label; };
static constexpr Stage STAGES[5] = {
	{2, 2, "Buf 2/2"},
	{4, 4, "Buf 4/4"},
	{8, 8, "Buf 8/8"},
	{16, 8, "Buf 16/8"},
	{0, 0, "Buf OFF"},
};

static int g_stage = 0;
static int g_tick = 0;
static std::vector<RingObject*> g_rings;
static std::vector<GameObject*> g_hazards;
static std::vector<GameObject*> g_solids;

struct PlayerBuf {
	// aros
	bool pressPending = false;
	int pressTick = 0;
	bool deferred = false;
	int deferTick = 0;
	// wave: entrada retrasada
	bool queued = false;
	bool queuedDown = false;
	int applyTick = 0;
	// cinematica medida
	bool haveLast = false;
	float lastX = 0.f, lastY = 0.f;
	float vx = 0.f, vy = 0.f, ay = 0.f;
};
static PlayerBuf g_p[2];

static constexpr float RING_RADIUS = 30.f;

static void resetBuffer() {
	g_tick = 0;
	g_p[0] = PlayerBuf{};
	g_p[1] = PlayerBuf{};
}

static int allLimit()  { return STAGES[g_stage].all; }
static int waveLimit() { return STAGES[g_stage].wave; }

static bool optRing()  { return Mod::get()->getSettingValue<bool>("ring-buffer"); }
static bool optWave()  { return Mod::get()->getSettingValue<bool>("wave-buffer"); }
static bool optLog()   { return Mod::get()->getSettingValue<bool>("log-saves"); }

// ---------------------------------------------------------------- aros
static bool ringActivated(RingObject* r, bool p1) {
	return p1 ? r->m_hasBeenActivatedP1 : r->m_hasBeenActivatedP2;
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

	// radio del hitbox de la wave
	float half = 5.f * std::fabs(pl->getScaleX());
	{
		auto pr = pl->getObjectRect();
		if (pr.size.width > 1.f && pr.size.width < 30.f) half = pr.size.width / 2.f;
	}
	half += pad;

	// pendiente: |vy|/|vx| medida; si esta pegada a techo/suelo usar 1 (45 grados)
	float slope = 1.f;
	if (std::fabs(st.vy) > 0.01f) slope = std::fabs(st.vy) / vx;
	if (slope < 0.5f || slope > 3.f) slope = 1.f;

	float flip = pl->m_isUpsideDown ? -1.f : 1.f;
	float dirNew = (down ? 1.f : -1.f) * flip;
	float dirOld = -dirNew;

	// obstaculos cercanos (rects)
	std::vector<CCRect> near;
	float xMax = x0 + vx * H + 80.f;
	auto collect = [&](std::vector<GameObject*>& list) {
		for (auto* o : list) {
			if (!o) continue;
			float ox = o->getPositionX();
			if (ox < x0 - 80.f || ox > xMax) continue;
			near.push_back(o->getObjectRect());
		}
	};
	collect(g_hazards);
	if (useSolids) collect(g_solids);
	if (near.empty()) return 0;

	// ticks hasta el choque con retraso d (H+1 = no choca en el horizonte)
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

	int t0 = ttc(0);
	if (t0 > H) return 0; // ya es seguro

	int bestD = 0, bestT = t0;
	for (int d = 1; d <= limit; d++) {
		int t = ttc(d);
		if (t > bestT) { bestT = t; bestD = d; }
		if (t > H) { bestD = d; bestT = t; break; } // primer retraso totalmente seguro
	}
	return bestD;
}

// ---------------------------------------------------------------- hooks
class $modify(BufBaseGameLayer, GJBaseGameLayer) {
	void handleButton(bool down, int button, bool isPlayer1) {
		if (g_stage == 4 || button != 1) {
			return GJBaseGameLayer::handleButton(down, button, isPlayer1);
		}
		int i = isPlayer1 ? 0 : 1;
		auto& st = g_p[i];
		auto* pl = isPlayer1 ? m_player1 : m_player2;
		if (!pl) return GJBaseGameLayer::handleButton(down, button, isPlayer1);

		// si habia una entrada de wave retenida, aplicarla antes de la nueva
		if (st.queued) {
			st.queued = false;
			GJBaseGameLayer::handleButton(st.queuedDown, 1, isPlayer1);
		}

		// ---- WAVE
		if (pl->m_isDart && optWave()) {
			st.pressPending = false;
			st.deferred = false;
			int d = chooseWaveDelay(pl, st, down);
			if (d > 0) {
				st.queued = true;
				st.queuedDown = down;
				st.applyTick = g_tick + d;
				if (optLog()) {
					log::info("[InputBuffer] WAVE {} delayed +{} ticks ({:.2f} frames @ 60fps) [Limit: {}]",
						down ? "press" : "release", d, d / 4.f, waveLimit());
				}
				return;
			}
			return GJBaseGameLayer::handleButton(down, button, isPlayer1);
		}

		// ---- ARO / ORBE
		if (!optRing()) return GJBaseGameLayer::handleButton(down, button, isPlayer1);

		if (down) {
			st.pressTick = g_tick;
			if (predictRingAhead(pl, st, isPlayer1, allLimit())) {
				st.deferred = true;
				st.deferTick = g_tick;
				st.pressPending = false;
				return;
			}
			st.pressPending = true;
			return GJBaseGameLayer::handleButton(true, button, isPlayer1);
		}

		if (st.deferred) {
			st.deferred = false;
			GJBaseGameLayer::handleButton(true, button, isPlayer1);
		}
		st.pressPending = false;
		GJBaseGameLayer::handleButton(false, button, isPlayer1);
	}

	void processCommands(float dt) {
		g_tick++;
		if (g_stage != 4) {
			for (int i = 0; i < 2; i++) {
				auto& st = g_p[i];
				if (st.queued && g_tick >= st.applyTick) {
					st.queued = false;
					GJBaseGameLayer::handleButton(st.queuedDown, 1, i == 0);
				}
				if (st.deferred && g_tick - st.deferTick >= allLimit()) {
					st.deferred = false;
					st.pressPending = true;
					st.pressTick = g_tick;
					GJBaseGameLayer::handleButton(true, 1, i == 0);
				}
				if (st.pressPending && g_tick - st.pressTick > allLimit()) {
					st.pressPending = false;
				}
			}
		}

		GJBaseGameLayer::processCommands(dt);

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
		if (g_stage == 4 || !optRing()) return;

		int i = (player == m_player1) ? 0 : 1;
		auto& st = g_p[i];

		bool fire = false;
		int saved = 0;
		if (st.deferred) {
			fire = true;
			saved = g_tick - st.deferTick;
			st.deferred = false;
		} else if (st.pressPending && g_tick - st.pressTick <= allLimit()) {
			fire = true;
			saved = g_tick - st.pressTick;
		}
		if (fire) {
			st.pressPending = false;
			GJBaseGameLayer::handleButton(true, 1, i == 0);
			if (optLog()) {
				log::info("[InputBuffer] RING SAVED +{} ticks ({:.2f} frames @ 60fps) [Limit: {}]",
					saved, saved / 4.f, allLimit());
			}
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
		if (g_stage < 0 || g_stage > 4) g_stage = 0;

		if (!Mod::get()->getSettingValue<bool>("show-button")) return;

		auto label = CCLabelBMFont::create(STAGES[g_stage].label, "bigFont.fnt");
		label->setScale(0.45f);
		label->setOpacity(160);
		auto btn = CCMenuItemExt::createSpriteExtra(label, [label](CCObject*) {
			g_stage = (g_stage + 1) % 5;
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

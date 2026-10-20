// Predictive Input Buffer v1.6 - simulacion de rutas por vehiculo (Windows / Android)
//
// Etapas (ticks a 240 Hz): 2/2 -> 4/4 -> 8/8 -> 16/8 -> 32/16 -> 64/32 -> OFF  (all / hold)
//   "all"  = ventana para cubo, UFO y swing.   "hold" = ventana para wave y nave.
//
// Idea general: el buffer solo toca un input si NINGUNA ruta razonable sobrevive con el
// input original, y existe un retraso (1..limite ticks) con el que alguna ruta si sobrevive.
//  - El modelo de fisica de cada vehiculo se APRENDE midiendo al jugador mientras juegas.
//  - "Mas rutas": el futuro del jugador se prueba con varias continuaciones (seguir
//    manteniendo, o cambiar de input despues de k ticks, k = 1..24).
//  - Un input es "malo" solo si todas esas rutas chocan con un hazard.
// Vehiculos simulados: wave, nave, UFO, swing y cubo (salto desde el suelo).
// Ademas (todos los modos): buffer de aros/orbes y de aterrizaje (cubo/bola/spider).
#include <Geode/Geode.hpp>
#include <Geode/modify/GJBaseGameLayer.hpp>
#include <Geode/modify/PlayLayer.hpp>
#include <algorithm>
#include <chrono>
#include <cmath>
#include <string>
#include <unordered_set>
#include <vector>

using namespace geode::prelude;

// ================================================================ etapas
struct Stage { int all; int hold; const char* label; };
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

// ================================================================ ajustes
static bool optRing()    { return Mod::get()->getSettingValue<bool>("ring-buffer"); }
static bool optLand()    { return Mod::get()->getSettingValue<bool>("land-buffer"); }
static bool optWave()    { return Mod::get()->getSettingValue<bool>("wave-buffer"); }
static bool optVeh()     { return Mod::get()->getSettingValue<bool>("vehicle-buffer"); }
static bool optSpam()    { return Mod::get()->getSettingValue<bool>("spam-guard"); }
static bool optHud()     { return Mod::get()->getSettingValue<bool>("hud-readout"); }
static bool optVerbose() { return Mod::get()->getSettingValue<bool>("hud-verbose"); }
static bool optLog()     { return Mod::get()->getSettingValue<bool>("log-saves"); }

// ================================================================ panel de log en pantalla
static std::vector<std::string> g_hudLines;
static CCLabelBMFont* g_hud = nullptr;
static bool g_hudDirty = false;
static std::string g_last; // ultima decision, para el reporte al reiniciar

static void hudLog(const std::string& s) {
	g_last = s;
	if (optLog()) log::info("[InputBuffer] {}", s);
	if (!optHud()) return;
	g_hudLines.push_back(s);
	size_t maxLines = (size_t)std::max<int64_t>(3, Mod::get()->getSettingValue<int64_t>("hud-lines"));
	while (g_hudLines.size() > maxLines) g_hudLines.erase(g_hudLines.begin());
	g_hudDirty = true;
}

// ================================================================ vehiculos y modelo aprendido
enum class Mode { None = 0, Wave, Ship, Ufo, Swing, Cube };
static const char* modeName(Mode m) {
	switch (m) {
		case Mode::Wave:  return "WAVE";
		case Mode::Ship:  return "SHIP";
		case Mode::Ufo:   return "UFO";
		case Mode::Swing: return "SWING";
		case Mode::Cube:  return "CUBE";
		default:          return "-";
	}
}

static Mode modeOf(PlayerObject* pl) {
	if (!pl) return Mode::None;
	if (pl->m_isDart)  return Mode::Wave;
	if (pl->m_isShip)  return Mode::Ship;
	if (pl->m_isBird)  return Mode::Ufo;
	if (pl->m_isSwing) return Mode::Swing;
	if (pl->m_isBall || pl->m_isRobot || pl->m_isSpider) return Mode::None;
	return Mode::Cube;
}

// cubo, bola y spider (modos donde saltar necesita estar en el suelo)
static bool groundMode(PlayerObject* pl) {
	return !(pl->m_isShip || pl->m_isBird || pl->m_isDart || pl->m_isRobot || pl->m_isSwing);
}

// parametros aprendidos (en unidades de "pixeles por tick", normalizados con la gravedad)
struct Learn {
	float aHold = 0.f, aFree = 0.f;   // nave: aceleracion con/sin mantener
	float jump = 0.f;                 // UFO / cubo: velocidad tras saltar
	float g = 0.f;                    // UFO / cubo: gravedad (swing: magnitud)
	float vmax = 0.f;                 // velocidad vertical maxima observada
	int nHold = 0, nFree = 0, nJump = 0, nG = 0;
};
static Learn g_learn[2][6];

struct WaveCmd { bool down; int tick; };

struct PlayerBuf {
	// press recordado (aros / aterrizaje)
	bool pending = false;
	bool deferred = false;
	bool released = false;
	bool landPending = false;
	int pendTick = 0;
	// cola de comandos retrasados (se conserva el orden)
	std::vector<WaveCmd> queue;
	bool lastDown = false;
	bool applied = false;     // ultimo estado realmente enviado al juego
	int sincePress = 99;
	bool wasGround = false;
	// guarda anti-spam
	int lastInputTick = -1000;
	int streak = 0;
	// cinematica medida
	bool haveLast = false;
	float lastX = 0.f, lastY = 0.f;
	float vx = 0.f, vy = 0.f, ay = 0.f;
	// avisos de "modelo no listo" ya mostrados
	bool warned[6] = {false, false, false, false, false, false};
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
static int holdLimit() { return STAGES[g_stage].hold; }
static int limitFor(Mode m) {
	return (m == Mode::Wave || m == Mode::Ship) ? holdLimit() : allLimit();
}

// ================================================================ aprendizaje de fisica
static void ema(float& v, int& n, float x) {
	v = n ? v * 0.8f + x * 0.2f : x;
	n = std::min(n + 1, 1000);
}

static void learnPhysics(int i, PlayerObject* pl) {
	auto& st = g_p[i];
	Mode m = modeOf(pl);
	if (m == Mode::None || m == Mode::Wave) { st.wasGround = pl->m_isOnGround; return; }
	auto& L = g_learn[i][(int)m];
	float f = pl->m_isUpsideDown ? -1.f : 1.f;
	float vyn = st.vy * f;
	float ayn = st.ay * f;
	bool air = !pl->m_isOnGround;

	switch (m) {
		case Mode::Ship:
			if (air) {
				if (st.applied) ema(L.aHold, L.nHold, ayn);
				else ema(L.aFree, L.nFree, ayn);
				L.vmax = std::max(L.vmax * 0.9995f, std::fabs(vyn));
			}
			break;
		case Mode::Ufo:
			if (air) {
				if (st.sincePress == 1) ema(L.jump, L.nJump, vyn);
				else if (st.sincePress >= 3) ema(L.g, L.nG, ayn);
				L.vmax = std::max(L.vmax * 0.9995f, std::fabs(vyn));
			}
			break;
		case Mode::Cube:
			if (st.wasGround && air && vyn > 0.5f) ema(L.jump, L.nJump, vyn);
			else if (air && !st.wasGround && std::fabs(ayn) > 0.0001f) ema(L.g, L.nG, ayn);
			break;
		case Mode::Swing:
			if (air && st.sincePress >= 3 && std::fabs(ayn) > 0.0001f) {
				ema(L.g, L.nG, std::fabs(ayn));
				L.vmax = std::max(L.vmax * 0.9995f, std::fabs(vyn));
			}
			break;
		default: break;
	}
	st.wasGround = pl->m_isOnGround;
}

// ================================================================ aros (prediccion lineal)
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

// ================================================================ simulacion de rutas
static bool boxHit(const CCRect& r, float x, float y, float h) {
	return !(x + h < r.origin.x || x - h > r.origin.x + r.size.width ||
	         y + h < r.origin.y || y - h > r.origin.y + r.size.height);
}

struct SimCtx {
	Mode mode;
	float x0, vx, f, slope, half;
	float yn0, vyn0;          // y y vy normalizados (f aplicado)
	bool prevDown, firstDown;
	bool grounded;
	float swingDir0;
	int H;
	const Learn* L;
	const std::vector<CCRect>* rects;
};

// Simula H ticks. Entrada: prevDown durante `d` ticks, luego firstDown. Si futureK > 0, tras
// futureK ticks de firstDown el jugador vuelve a prevDown (un "tap" o cambio posterior).
static bool survives(const SimCtx& c, int d, int futureK) {
	float x = c.x0;
	float yn = c.yn0, vyn = c.vyn0;
	bool prev = c.prevDown;
	bool grounded = c.grounded;
	float dirG = c.swingDir0;
	const Learn& L = *c.L;

	for (int k = 1; k <= c.H; k++) {
		bool in;
		if (k <= d) in = c.prevDown;
		else if (futureK > 0 && k > d + futureK) in = c.prevDown;
		else in = c.firstDown;
		bool edge = (in != prev);
		prev = in;

		switch (c.mode) {
			case Mode::Wave:
				yn += (in ? 1.f : -1.f) * c.slope * c.vx;
				break;
			case Mode::Ship:
				vyn += in ? L.aHold : L.aFree;
				if (L.vmax > 0.f) vyn = std::max(-L.vmax, std::min(L.vmax, vyn));
				yn += vyn;
				break;
			case Mode::Ufo:
				if (edge && in) vyn = L.jump; else vyn += L.g;
				if (L.vmax > 0.f) vyn = std::max(-L.vmax, std::min(L.vmax, vyn));
				yn += vyn;
				break;
			case Mode::Swing:
				if (edge && in) dirG = -dirG;
				vyn += dirG * L.g;
				if (L.vmax > 0.f) vyn = std::max(-L.vmax, std::min(L.vmax, vyn));
				yn += vyn;
				break;
			case Mode::Cube:
				if (grounded) {
					if (in) { vyn = L.jump; grounded = false; yn += vyn; }
				} else {
					vyn += L.g;
					yn += vyn;
					if (yn <= c.yn0) { yn = c.yn0; vyn = 0.f; grounded = true; }
				}
				break;
			default: break;
		}
		x += c.vx;
		float y = yn * c.f;
		for (auto& r : *c.rects) {
			if (boxHit(r, x, y, c.half)) return false;
		}
	}
	return true;
}

static constexpr int FUTURE_K[] = {0, 1, 2, 3, 4, 6, 8, 12, 16, 24};

// true si ALGUNA ruta futura razonable sobrevive con retraso d
static bool anyRouteSurvives(const SimCtx& c, int d) {
	for (int k : FUTURE_K) {
		if (k > c.H) break;
		if (survives(c, d, k)) return true;
	}
	return false;
}

// Elige cuantos ticks retrasar el input (0 = pasa al instante).
static int chooseDelay(Mode m, PlayerObject* pl, PlayerBuf& st, int idx, bool down) {
	int limit = limitFor(m);
	if (!pl || !st.haveLast || limit <= 0) return 0;
	float vx = std::fabs(st.vx);
	if (vx < 0.01f) return 0;

	auto& L = g_learn[idx][(int)m];
	bool ready = true;
	switch (m) {
		case Mode::Ship:  ready = L.nHold >= 6 && L.nFree >= 6; break;
		case Mode::Ufo:   ready = L.nJump >= 1 && L.nG >= 6; break;
		case Mode::Cube:  ready = pl->m_isOnGround && L.nJump >= 1 && L.nG >= 6; break;
		case Mode::Swing: ready = L.nG >= 6; break;
		default: break;
	}
	if (!ready) {
		if (m == Mode::Cube && !pl->m_isOnGround) return 0; // lo cubre el buffer de aterrizaje
		if (!st.warned[(int)m]) {
			st.warned[(int)m] = true;
			hudLog(std::string(modeName(m)) + ": aprendiendo fisica (sin ajuste todavia)");
		}
		return 0;
	}

	auto t0 = std::chrono::steady_clock::now();
	int64_t budgetUs = Mod::get()->getSettingValue<int64_t>("cpu-budget-us");
	auto over = [&]() {
		if (budgetUs <= 0) return false;
		auto us = std::chrono::duration_cast<std::chrono::microseconds>(
			std::chrono::steady_clock::now() - t0).count();
		return us > budgetUs;
	};

	SimCtx c{};
	c.mode = m;
	c.H = (int)Mod::get()->getSettingValue<int64_t>("wave-horizon");
	c.f = pl->m_isUpsideDown ? -1.f : 1.f;
	c.x0 = pl->getPositionX();
	c.vx = vx;
	c.yn0 = pl->getPositionY() * c.f;
	c.vyn0 = st.vy * c.f;
	c.prevDown = st.applied;
	c.firstDown = down;
	c.grounded = pl->m_isOnGround;
	c.swingDir0 = (st.ay * c.f >= 0.f) ? 1.f : -1.f;
	c.L = &L;

	float slope = 1.f;
	if (std::fabs(st.vy) > 0.01f) slope = std::fabs(st.vy) / vx;
	if (slope < 0.5f || slope > 3.f) slope = 1.f;
	c.slope = slope;

	float scale = std::fabs(pl->getScaleX());
	float half = (m == Mode::Wave ? 5.f : 15.f) * scale;
	{
		auto pr = pl->getObjectRect();
		if (pr.size.width > 2.f && pr.size.width < 45.f) half = pr.size.width / 2.f;
	}
	half += (float)Mod::get()->getSettingValue<double>("wave-padding");
	c.half = half;

	// obstaculos cercanos
	std::vector<CCRect> near;
	float xMax = c.x0 + vx * c.H + 80.f;
	auto collect = [&](std::vector<GameObject*>& list) {
		for (auto* o : list) {
			if (!o) continue;
			float ox = o->getPositionX();
			if (ox < c.x0 - 80.f || ox > xMax) continue;
			CCRect r = o->getObjectRect();
			r.origin.x += 1.f; r.origin.y += 1.f;
			r.size.width -= 2.f; r.size.height -= 2.f;
			near.push_back(r);
		}
	};
	collect(g_hazards);
	if (m == Mode::Wave && Mod::get()->getSettingValue<bool>("wave-solids")) collect(g_solids);
	if (near.empty()) return 0;
	c.rects = &near;

	// 1) con retraso 0 sobrevive alguna ruta? -> pasa intacto
	if (anyRouteSurvives(c, 0)) {
		if (optVerbose()) hudLog(std::string(modeName(m)) + (down ? " v" : " ^") + " ok (raw)");
		return 0;
	}

	// 2) ninguna ruta sobrevive: buscar el primer retraso que salve alguna ruta
	int best = 0;
	for (int d = 1; d <= limit; d++) {
		if (over()) { hudLog(std::string(modeName(m)) + ": limite de CPU, input crudo"); return 0; }
		if (anyRouteSurvives(c, d)) { best = d; break; }
	}
	if (best == 0) {
		hudLog(std::string(modeName(m)) + (down ? " v" : " ^") + " sin salida (crudo)");
		return 0;
	}

	// 3) margen de seguridad (no en wave)
	if (m != Mode::Wave) {
		int margin = (int)Mod::get()->getSettingValue<int64_t>("safety-ticks");
		if (margin > 0 && best + margin <= limit && anyRouteSurvives(c, best + margin)) best += margin;
	}

	hudLog(std::string(modeName(m)) + (down ? " v" : " ^") + " +" + std::to_string(best) +
		"t (" + std::to_string(best / 4.f).substr(0, 4) + "f)");
	return best;
}

// ================================================================ guarda anti-spam
static bool registerInput(PlayerBuf& st) {
	int guard = (int)(Mod::get()->getSettingValue<double>("spam-frames") * 4.0);
	int need = (int)Mod::get()->getSettingValue<int64_t>("spam-streak");
	if (g_tick - st.lastInputTick <= guard) st.streak++; else st.streak = 1;
	st.lastInputTick = g_tick;
	return optSpam() && st.streak >= need;
}

// ================================================================ hooks
class $modify(BufBaseGameLayer, GJBaseGameLayer) {
	// envia un boton al juego y recuerda el estado real
	void sendButton(bool down, int i) {
		auto& st = g_p[i];
		if (down && !st.applied) st.sincePress = 0;
		st.applied = down;
		GJBaseGameLayer::handleButton(down, 1, i == 0);
	}

	// envia un press ahora; si el jugador ya habia soltado, encola el release 1 tick despues
	void firePress(int i, bool alsoRelease) {
		sendButton(true, i);
		if (alsoRelease) g_p[i].queue.push_back({false, g_tick + 1});
	}

	void clearPending(PlayerBuf& st) {
		st.pending = false;
		st.deferred = false;
		st.landPending = false;
		st.released = false;
	}

	void handleButton(bool down, int button, bool isPlayer1) {
		int i = isPlayer1 ? 0 : 1;
		auto& st = g_p[i];

		if (g_stage == OFF_STAGE || button != 1) {
			if (button == 1) {
				if (down && !st.applied) st.sincePress = 0;
				st.applied = down;
			}
			return GJBaseGameLayer::handleButton(down, button, isPlayer1);
		}
		auto* pl = isPlayer1 ? m_player1 : m_player2;
		if (!pl) {
			st.applied = down;
			return GJBaseGameLayer::handleButton(down, button, isPlayer1);
		}

		bool spam = registerInput(st);

		// entradas retenidas: esta va detras (no se altera el orden)
		if (!st.queue.empty()) {
			int t = std::max(g_tick, st.queue.back().tick + 1);
			st.queue.push_back({down, t});
			st.lastDown = down;
			return;
		}

		// ---- vehiculos con simulacion de rutas
		Mode m = modeOf(pl);
		bool predictive = (m == Mode::Wave && optWave()) ||
			((m == Mode::Ship || m == Mode::Ufo || m == Mode::Swing || m == Mode::Cube) && optVeh());
		if (predictive) {
			clearPending(st);
			bool matters = !((m == Mode::Ufo || m == Mode::Swing || m == Mode::Cube) && !down);
			bool redundant = (down == st.applied);
			st.lastDown = down;
			if (matters && !redundant) {
				if (spam) {
					if (optVerbose()) hudLog(std::string(modeName(m)) + ": spam, input crudo");
				} else {
					int d = chooseDelay(m, pl, st, i, down);
					if (d > 0) {
						st.queue.push_back({down, g_tick + d});
						return;
					}
				}
			}
			if (m == Mode::Wave) {
				sendButton(down, i);
				return;
			}
			// los demas vehiculos siguen con aros/aterrizaje abajo
		}
		st.lastDown = down;

		bool ring = optRing();
		bool land = optLand();
		if (!ring && !land) { sendButton(down, i); return; }

		// ---- PRESS
		if (down) {
			clearPending(st);
			st.pendTick = g_tick;

			if (ring && predictRingAhead(pl, st, isPlayer1, allLimit())) {
				st.pending = true;
				st.deferred = true;
				if (land && groundMode(pl) && !pl->m_isOnGround) st.landPending = true;
				return;
			}
			st.pending = true;
			if (land && groundMode(pl) && !pl->m_isOnGround) st.landPending = true;
			sendButton(true, i);
			return;
		}

		// ---- RELEASE
		st.released = true;
		if (st.deferred) return; // se emitira junto con el press diferido
		sendButton(false, i);
	}

	void processCommands(float dt, bool isHalfTick, bool isLastTick) {
		if (!isHalfTick) g_tick++;

		if (!isHalfTick) {
			PlayerObject* players[2] = {m_player1, m_player2};
			for (int i = 0; i < 2; i++) {
				auto& st = g_p[i];
				auto* pl = players[i];
				if (st.sincePress < 99) st.sincePress++;

				// 1) comandos retrasados (uno por tick, en orden)
				if (!st.queue.empty() && g_tick >= st.queue.front().tick) {
					WaveCmd c = st.queue.front();
					st.queue.erase(st.queue.begin());
					sendButton(c.down, i);
				}

				if (g_stage == OFF_STAGE || !st.pending) continue;

				// 2) expiro la ventana
				if (g_tick - st.pendTick > allLimit()) {
					if (st.deferred) firePress(i, st.released);
					clearPending(st);
					continue;
				}

				// 3) aterrizaje (cubo/bola/spider) con el boton ya soltado
				if (st.landPending && pl && pl->m_isOnGround) {
					if (st.released && !st.deferred) {
						int saved = g_tick - st.pendTick;
						firePress(i, true);
						hudLog("LAND +" + std::to_string(saved) + "t");
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
				learnPhysics(i, pl);
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
		firePress(i, wasReleased);
		hudLog("RING +" + std::to_string(saved) + "t");
	}
};

class $modify(BufPlayLayer, PlayLayer) {
	void setupHasCompleted() {
		PlayLayer::setupHasCompleted();
		resetBuffer();
		g_hudLines.clear();
		g_hud = nullptr;

		g_rings.clear();
		g_hazards.clear();
		g_solids.clear();
		if (m_objects) {
			for (auto* obj : C

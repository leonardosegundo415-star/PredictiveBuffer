// Predictive Input Buffer v2.0 - simulacion de rutas por vehiculo (Windows / Android)
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
#include <cstdio>
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
static std::vector<GameObject*> g_slopes;

// ================================================================ ajustes
static bool optRing() { return Mod::get()->getSettingValue<bool>("ring-buffer"); }
static bool optLand() { return Mod::get()->getSettingValue<bool>("land-buffer"); }
static bool optWave() { return Mod::get()->getSettingValue<bool>("wave-buffer"); }
static bool optVeh()  { return Mod::get()->getSettingValue<bool>("vehicle-buffer"); }
static bool optHud()  { return Mod::get()->getSettingValue<bool>("hud-readout"); }

// Todo lo demas es automatico (pensado para celular).
static constexpr int   SPAM_TICKS   = 4;    // inputs a <= 4 ticks (1 frame @60) cuentan como spam...
static constexpr int   SPAM_STREAK  = 5;    // ...solo tras 5 seguidos
static constexpr int   SAFETY_TICKS = 1;    // margen extra tras hallar el retraso
static constexpr int   HUD_LINES    = 5;
static constexpr float MARGIN_WAVE  = 2.0f; // holgura (px) que se exige a las rutas
static constexpr float MARGIN_OTHER = 3.0f;

// presupuesto de CPU automatico: ~25% del tiempo de frame medido (entre 0.5 y 4 ms)
static double g_frameUs = 8333.0;
static std::chrono::steady_clock::time_point g_lastFrame;
static bool g_haveFrame = false;
static int64_t autoBudgetUs() {
	double b = g_frameUs * 0.25;
	return (int64_t)std::max(500.0, std::min(4000.0, b));
}

// ================================================================ panel de log en pantalla
static std::vector<std::string> g_hudLines;
static CCLabelBMFont* g_hud = nullptr;
static bool g_hudDirty = false;
static std::string g_last; // ultima decision, para el reporte al reiniciar

static void hudLog(const std::string& s, bool track = true) {
	if (track) g_last = s;
	log::info("[InputBuffer] {}", s);
	if (!optHud()) return;
	g_hudLines.push_back(s);
	while (g_hudLines.size() > (size_t)HUD_LINES) g_hudLines.erase(g_hudLines.begin());
	g_hudDirty = true;
}

// ================================================================ overlay de depuracion
// Dibuja lo que el mod "ve": hazards (amarillo), bloques (naranja), hitbox del jugador (blanco),
// ruta cruda (rojo, hasta el choque) y ruta con retraso elegido (verde).
static bool g_overlay = false;
static CCDrawNode* g_draw = nullptr;
static std::vector<CCPoint> g_pathRaw, g_pathBest;
static float g_dbgHalf = 0.f;

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

// ---- base de tiempo: se mide cuantas veces por segundo corre processCommands.
// Las etapas estan definidas en "ticks" de 1/240 s; aqui se convierten a llamadas reales.
static double g_cps = 240.0;
static int g_cpsCount = 0;
static bool g_cpsStarted = false;
static bool g_cpsHave = false;
static std::chrono::steady_clock::time_point g_cpsStart;

static void sampleCps() {
	auto now = std::chrono::steady_clock::now();
	if (!g_cpsStarted) { g_cpsStarted = true; g_cpsStart = now; g_cpsCount = 0; return; }
	g_cpsCount++;
	double el = std::chrono::duration<double>(now - g_cpsStart).count();
	if (el >= 0.5) {
		if (g_cpsCount >= 20) {
			double v = g_cpsCount / el;
			if (v > 30.0 && v < 2000.0) { g_cps = g_cpsHave ? g_cps * 0.6 + v * 0.4 : v; g_cpsHave = true; }
		}
		g_cpsStart = now;
		g_cpsCount = 0;
	}
}
static int toCalls(int ticks240) {
	if (ticks240 <= 0) return 0;
	return std::max(1, (int)std::lround(ticks240 * g_cps / 240.0));
}
// constantes de GD estan en unidades por frame a 60 fps; se pasan a "por llamada"
static float perCallV(float v60) { return (float)(v60 * 60.0 / g_cps); }
static float perCallA(float a60) { double k = 60.0 / g_cps; return (float)(a60 * k * k); }

static int g_lastMsg[6] = {-100000, -100000, -100000, -100000, -100000, -100000};
static bool canLog(int mode) {
	if (g_tick - g_lastMsg[mode] < toCalls(240)) return false; // 1 mensaje por segundo y modo
	g_lastMsg[mode] = g_tick;
	return true;
}

static void resetBuffer() {
	g_tick = 0;
	g_p[0] = PlayerBuf{};
	g_p[1] = PlayerBuf{};
	g_touched[0].clear();
	g_touched[1].clear();
	for (int& v : g_lastMsg) v = -100000;
}

static int allLimit()  { return toCalls(STAGES[g_stage].all); }
static int holdLimit() { return toCalls(STAGES[g_stage].hold); }
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

	// rechazar muestras absurdas (respawn, teletransporte, portales)
	if (std::fabs(vyn) > perCallV(12.f) || std::fabs(ayn) > perCallA(1.2f)) {
		st.wasGround = pl->m_isOnGround;
		return;
	}

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

// rampa: segmento de hipotenusa (y0 en el borde izquierdo, y1 en el derecho) dentro de su rect
struct SlopeSeg {
	CCRect r;
	float y0, y1;
	bool floor; // true = el solido esta DEBAJO de la hipotenusa (se pisa por arriba)
};

struct SimCtx {
	Mode mode;
	float x0, vx, f, slope, half;
	float yn0, vyn0;          // y y vy normalizados (f aplicado)
	bool prevDown, firstDown;
	bool grounded;
	float swingDir0;
	int H;
	const Learn* L;
	const std::vector<CCRect>* rects;   // hazards (letales al tocar)
	const std::vector<CCRect>* solids;  // bloques solidos (wave: letal de lado, desliza por arriba/abajo)
	const std::vector<SlopeSeg>* slopes; // rampas (triangulos)
};

// Simula H ticks. Entrada: prevDown durante `d` ticks, luego firstDown. Si futureK > 0, tras
// futureK ticks de firstDown el jugador vuelve a prevDown (un "tap" o cambio posterior).
static bool survives(const SimCtx& c, int d, int futureK, std::vector<CCPoint>* trace = nullptr) {
	float x = c.x0;
	float yn = c.yn0, vyn = c.vyn0;
	bool prev = c.prevDown;
	bool grounded = c.grounded;
	float floorN = c.yn0;   // suelo actual (cubo): sube al aterrizar sobre un bloque
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
					if (yn <= floorN) { yn = floorN; vyn = 0.f; grounded = true; }
				}
				break;
			default: break;
		}
		x += c.vx;
		float y = yn * c.f;

		// bloques solidos (todos los vehiculos): golpe de lado = muerte; por arriba/abajo desliza o aterriza
		if (c.solids) {
			for (auto& r : *c.solids) {
				float ox = std::min(x + c.half, r.origin.x + r.size.width) - std::max(x - c.half, r.origin.x);
				float oy = std::min(y + c.half, r.origin.y + r.size.height) - std::max(y - c.half, r.origin.y);
				if (ox > 0.f && oy > 0.f) {
					if (ox < oy * 0.8f) return false; // choque de lado
					float cy = r.origin.y + r.size.height * 0.5f;
					bool fromTop = (y >= cy);
					y = fromTop ? (r.origin.y + r.size.height + c.half) : (r.origin.y - c.half);
					yn = y * c.f;
					if (c.mode != Mode::Wave) vyn = 0.f;
					if (c.mode == Mode::Cube && ((c.f > 0.f) == fromTop)) { grounded = true; floorN = yn; }
				}
			}
		}
		// rampas: se desliza por la hipotenusa; un golpe contra su pared mata
		if (c.slopes) {
			for (auto& sg : *c.slopes) {
				const CCRect& r = sg.r;
				float ox = std::min(x + c.half, r.origin.x + r.size.width) - std::max(x - c.half, r.origin.x);
				float oy = std::min(y + c.half, r.origin.y + r.size.height) - std::max(y - c.half, r.origin.y);
				if (ox <= 0.f || oy <= 0.f) continue;
				bool up = sg.y1 > sg.y0;
				float cx = sg.floor ? (up ? x + c.half : x - c.half) : (up ? x - c.half : x + c.half);
				cx = std::max(r.origin.x, std::min(r.origin.x + r.size.width, cx));
				float t = (r.size.width > 0.f) ? (cx - r.origin.x) / r.size.width : 0.f;
				float hy = sg.y0 + (sg.y1 - sg.y0) * t;
				float pen = sg.floor ? (hy - (y - c.half)) : ((y + c.half) - hy);
				if (pen <= 0.f) continue;
				if (pen > 2.5f * c.vx + 2.f) return false; // pared de la rampa
				y += sg.floor ? pen : -pen;
				yn = y * c.f;
				if (c.mode != Mode::Wave) vyn = 0.f;
				if (c.mode == Mode::Cube && ((c.f > 0.f) == sg.floor)) { grounded = true; floorN = yn; }
			}
		}
		if (trace && trace->size() < 80) trace->push_back(CCPoint{x, y});
		for (auto& r : *c.rects) {
			if (boxHit(r, x, y, c.half)) return false;
		}
	}
	return true;
}

// futuros que se prueban: sin mas cambios, o un cambio de input tras k ticks.
// No se cuentan correcciones inmediatas (k = 1..6): no son humanas.
static constexpr int FUTURE_K[] = {0, 8, 12, 16, 24};

// true si ALGUNA ruta futura razonable sobrevive con retraso d
static bool anyRouteSurvives(const SimCtx& c, int d) {
	for (int k0 : FUTURE_K) {
		int k = k0 ? toCalls(k0) : 0;
		if (k > c.H) break;
		if (survives(c, d, k)) return true;
	}
	return false;
}

// Lee la geometria de una rampa usando las funciones del propio juego.
// Devuelve false si la rampa es degenerada.
static bool slopeInfo(GameObject* o, SlopeSeg& out) {
	if (!o) return false;
	CCRect r = o->getObjectRect();
	if (r.size.width < 1.f || r.size.height < 1.f) return false;
	float y0 = (float)o->slopeYPos(r.origin.x);
	float y1 = (float)o->slopeYPos(r.origin.x + r.size.width);
	bool up = y1 > y0;
	bool wallLeft = o->slopeWallLeft();
	// suelo = solido debajo de la hipotenusa: pared a la izquierda si baja hacia la derecha
	bool floorTop = (wallLeft && !up) || (!wallLeft && up);
	out.r = r;
	out.y0 = y0;
	out.y1 = y1;
	out.floor = floorTop;
	return true;
}

// Elige cuantos ticks retrasar el input (0 = pasa al instante).
//  - Si con retraso 0 ninguna ruta sobrevive (choque seguro): busca el primer retraso que salve.
//  - Si sobrevive pero rozando (no aguanta una holgura extra): busca un retraso que de holgura.
static int chooseDelay(Mode m, PlayerObject* pl, PlayerBuf& st, int idx, bool down) {
	int limit = limitFor(m);
	if (!pl || !st.haveLast || limit <= 0) return 0;
	float vx = std::fabs(st.vx);
	if (vx < 0.01f) return 0;

	Learn Lp = g_learn[idx][(int)m];
	auto& L = Lp;
	bool ready = true;
	if (m == Mode::Cube) {
		// valores conocidos del juego (por frame a 60 fps), convertidos a "por llamada"
		float jPrior = perCallV(11.18f);
		float gPrior = -perCallA(0.958f);
		if (!(L.nJump >= 1 && L.jump > 0.6f * jPrior && L.jump < 1.4f * jPrior)) L.jump = jPrior;
		if (!(L.nG >= 6 && L.g < 0.6f * gPrior && L.g > 1.4f * gPrior)) L.g = gPrior;
		L.nJump = 1; L.nG = 6;
	}
	switch (m) {
		case Mode::Ship:  ready = L.nHold >= 6 && L.nFree >= 6; break;
		case Mode::Ufo:   ready = L.nJump >= 1 && L.nG >= 6; break;
		case Mode::Cube:  ready = pl->m_isOnGround; break;
		case Mode::Swing: ready = L.nG >= 6; break;
		default: break;
	}
	if (!ready) {
		if (m == Mode::Cube && !pl->m_isOnGround) return 0; // lo cubre el buffer de aterrizaje
		if (!st.warned[(int)m]) {
			st.warned[(int)m] = true;
			hudLog(std::string(modeName(m)) + ": aprendiendo fisica");
		}
		return 0;
	}

	auto t0 = std::chrono::steady_clock::now();
	int64_t budgetUs = autoBudgetUs();
	auto over = [&]() {
		auto us = std::chrono::duration_cast<std::chrono::microseconds>(
			std::chrono::steady_clock::now() - t0).count();
		return us > budgetUs;
	};

	SimCtx c{};
	c.mode = m;
	c.H = std::min(40, std::max(12, limit + 10));
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
	c.half = half;

	// obstaculos cercanos
	std::vector<CCRect> nearRects;   // hazards
	std::vector<CCRect> nearSolids;  // bloques (solo wave)
	float xMax = c.x0 + vx * c.H + 80.f;
	auto collect = [&](std::vector<GameObject*>& list, std::vector<CCRect>& out, bool shrink) {
		for (auto* o : list) {
			if (!o) continue;
			float ox = o->getPositionX();
			if (ox < c.x0 - 80.f || ox > xMax) continue;
			CCRect r = o->getObjectRect();
			if (shrink) {
				r.origin.x += 1.f; r.origin.y += 1.f;
				r.size.width -= 2.f; r.size.height -= 2.f;
			}
			out.push_back(r);
		}
	};
	collect(g_hazards, nearRects, true);
	bool useSolids = true;
	collect(g_solids, nearSolids, false);
	std::vector<SlopeSeg> nearSlopes;
	for (auto* o : g_slopes) {
		if (!o) continue;
		float ox = o->getPositionX();
		if (ox < c.x0 - 80.f || ox > xMax) continue;
		SlopeSeg sg;
		if (slopeInfo(o, sg)) nearSlopes.push_back(sg);
		if (nearSlopes.size() >= 48) break;
	}
	if (nearRects.empty() && nearSolids.empty() && nearSlopes.empty()) return 0;
	c.rects = &nearRects;
	c.solids = useSolids ? &nearSolids : nullptr;
	c.slopes = &nearSlopes;
	g_dbgHalf = c.half;

	// misma simulacion pero exigiendo holgura extra
	SimCtx cm = c;
	cm.half = c.half + (m == Mode::Wave ? MARGIN_WAVE : MARGIN_OTHER);

	if (g_overlay) {
		g_pathRaw.clear(); g_pathBest.clear();
		survives(c, 0, 0, &g_pathRaw);
	}

	// 1) seguro incluso con holgura: pasa intacto
	if (anyRouteSurvives(cm, 0)) return 0;

	// 2) con retraso 0: choque seguro, o solo rozando?
	bool lethal = !anyRouteSurvives(c, 0);

	int best = 0;
	for (int d = 1; d <= limit; d++) {
		if (over()) { if (canLog((int)m)) hudLog(std::string(modeName(m)) + ": limite de CPU (auto)"); return 0; }
		if (anyRouteSurvives(cm, d)) { best = d; break; }
	}
	if (best == 0 && lethal) {
		for (int d = 1; d <= limit; d++) {
			if (over()) { if (canLog((int)m)) hudLog(std::string(modeName(m)) + ": limite de CPU (auto)"); return 0; }
			if (anyRouteSurvives(c, d)) { best = d; break; }
		}
		if (best == 0) {
			if (canLog((int)m)) hudLog(std::string(modeName(m)) + (down ? " v" : " ^") + " sin salida");
			return 0;
		}
	}
	if (best == 0) return 0; // roce, pero ningun retraso mejora: crudo

	// 3) margen de seguridad (no en wave)
	if (m != Mode::Wave && best + SAFETY_TICKS <= limit &&
	    anyRouteSurvives(lethal ? c : cm, best + SAFETY_TICKS)) best += SAFETY_TICKS;

	if (g_overlay) {
		g_pathRaw.clear(); g_pathBest.clear();
		survives(c, 0, 0, &g_pathRaw);
		survives(c, best, 0, &g_pathBest);
	}
	{
		char buf[24];
		std::snprintf(buf, sizeof(buf), " +%dc %.1ff", best, best * 60.0 / g_cps);
		hudLog(std::string(modeName(m)) + (down ? " v" : " ^") + buf + (lethal ? " !" : " ~"));
	}
	return best;
}

// ================================================================ guarda anti-spam
// Solo se aparta con spam real: 5 inputs seguidos a menos de 1 frame entre si.
static bool registerInput(PlayerBuf& st) {
	if (g_tick - st.lastInputTick <= toCalls(SPAM_TICKS)) st.streak++; else st.streak = 1;
	st.lastInputTick = g_tick;
	return st.streak >= SPAM_STREAK;
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
				if (!spam) {
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
		if (!isHalfTick) { g_tick++; sampleCps(); }

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
				if (std::fabs(nvx) > 30.f || std::fabs(nvy) > 30.f) {
					// teletransporte (respawn / portal): descartar la medicion
					st.vx = 0.f; st.vy = 0.f; st.ay = 0.f;
				} else {
					st.ay = nvy - st.vy;
					st.vx = nvx;
					st.vy = nvy;
					learnPhysics(i, pl);
				}
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
		g_draw = nullptr;
		g_pathRaw.clear();
		g_pathBest.clear();

		g_rings.clear();
		g_hazards.clear();
		g_solids.clear();
		g_slopes.clear();
		if (m_objects) {
			for (auto* obj : CCArrayExt<GameObject*>(m_objects)) {
				if (!obj) continue;
				if (auto* ring = typeinfo_cast<RingObject*>(obj)) {
					g_rings.push_back(ring);
					continue;
				}
				if (obj->m_objectType == GameObjectType::Hazard) g_hazards.push_back(obj);
				else if (obj->m_objectType == GameObjectType::Solid) g_solids.push_back(obj);
				else if (obj->m_objectType == GameObjectType::Slope) {
					if (obj->m_slopeIsHazard) g_hazards.push_back(obj);
					else g_slopes.push_back(obj);
				}
			}
		}

		g_stage = Mod::get()->getSavedValue<int>("stage", 0);
		if (g_stage < 0 || g_stage >= STAGE_COUNT) g_stage = 0;

		// panel de log arriba a la derecha
		if (optHud()) {
			auto win = CCDirector::get()->getWinSize();
			g_hud = CCLabelBMFont::create("", "chatFont.fnt");
			g_hud->setAnchorPoint({1.f, 1.f});
			g_hud->setAlignment(kCCTextAlignmentRight);
			g_hud->setScale(0.55f);
			g_hud->setOpacity(210);
			g_hud->setPosition({win.width - 6.f, win.height - 6.f});
			this->addChild(g_hud, 201);
		}

		g_overlay = Mod::get()->getSavedValue<bool>("overlay", false);
		if (m_objectLayer) {
			g_draw = CCDrawNode::create();
			m_objectLayer->addChild(g_draw, 1000);
		}

		if (!Mod::get()->getSettingValue<bool>("show-button")) return;

		auto label = CCLabelBMFont::create(STAGES[g_stage].label, "bigFont.fnt");
		label->setScale(0.55f);
		label->setOpacity(200);
		auto btn = CCMenuItemExt::createSpriteExtra(label, [label](CCObject*) {
			g_stage = (g_stage + 1) % STAGE_COUNT;
			Mod::get()->setSavedValue<int>("stage", g_stage);
			label->setString(STAGES[g_stage].label);
			hudLog(std::string("Etapa -> ") + STAGES[g_stage].label);
		});
		auto verLabel = CCLabelBMFont::create(g_overlay ? "Ver ON" : "Ver", "bigFont.fnt");
		verLabel->setScale(0.55f);
		verLabel->setOpacity(200);
		auto verBtn = CCMenuItemExt::createSpriteExtra(verLabel, [verLabel](CCObject*) {
			g_overlay = !g_overlay;
			Mod::get()->setSavedValue<bool>("overlay", g_overlay);
			verLabel->setString(g_overlay ? "Ver ON" : "Ver");
			if (!g_overlay && g_draw) g_draw->clear();
		});
		auto menu = CCMenu::create();
		menu->setPosition({0, 0});
		btn->setPosition({55.f, 18.f});
		verBtn->setPosition({150.f, 18.f});
		menu->addChild(btn);
		menu->addChild(verBtn);
		this->addChild(menu, 200);
	}

	void postUpdate(float dt) {
		PlayLayer::postUpdate(dt);
		{
			auto now = std::chrono::steady_clock::now();
			if (g_haveFrame) {
				double us = (double)std::chrono::duration_cast<std::chrono::microseconds>(now - g_lastFrame).count();
				if (us > 2000.0 && us < 100000.0) g_frameUs = g_frameUs * 0.9 + us * 0.1;
			}
			g_lastFrame = now;
			g_haveFrame = true;
		}
		if (g_overlay && g_draw && m_player1) {
			g_draw->clear();
			float px = m_player1->getPositionX();
			float py = m_player1->getPositionY();
			auto box = [&](const CCRect& r, ccColor4F col) {
				CCPoint v[4] = {{r.origin.x, r.origin.y}, {r.origin.x + r.size.width, r.origin.y},
				                {r.origin.x + r.size.width, r.origin.y + r.size.height}, {r.origin.x, r.origin.y + r.size.height}};
				g_draw->drawPolygon(v, 4, ccColor4F{0.f, 0.f, 0.f, 0.f}, 1.0f, col);
			};
			int drawn = 0;
			for (auto* o : g_hazards) {
				if (!o || std::fabs(o->getPositionX() - px) > 260.f) continue;
				box(o->getObjectRect(), ccColor4F{1.f, 1.f, 0.f, 1.f});
				if (++drawn > 200) break;
			}
			drawn = 0;
			for (auto* o : g_solids) {
				if (!o || std::fabs(o->getPositionX() - px) > 260.f) continue;
				box(o->getObjectRect(), ccColor4F{1.f, 0.55f, 0.f, 1.f});
				if (++drawn > 200) break;
			}
			drawn = 0;
			for (auto* o : g_slopes) {
				if (!o || std::fabs(o->getPositionX() - px) > 260.f) continue;
				SlopeSeg sg;
				if (!slopeInfo(o, sg)) continue;
				const CCRect& r = sg.r;
				bool up = sg.y1 > sg.y0;
				CCPoint a{r.origin.x, sg.y0};
				CCPoint b{r.origin.x + r.size.width, sg.y1};
				CCPoint cc = sg.floor ? (up ? CCPoint{r.origin.x + r.size.width, r.origin.y} : CCPoint{r.origin.x, r.origin.y})
				                      : (up ? CCPoint{r.origin.x, r.origin.y + r.size.height} : CCPoint{r.origin.x + r.size.width, r.origin.y + r.size.height});
				CCPoint v[3] = {a, b, cc};
				g_draw->drawPolygon(v, 3, ccColor4F{0.f, 0.f, 0.f, 0.f}, 1.0f, ccColor4F{1.f, 0.f, 1.f, 1.f});
				if (++drawn > 120) break;
			}
			float h = g_dbgHalf > 0.f ? g_dbgHalf : 5.f;
			box(CCRect{CCPoint{px - h, py - h}, CCSize{2.f * h, 2.f * h}}, ccColor4F{1.f, 1.f, 1.f, 1.f});
			for (size_t k = 1; k < g_pathRaw.size(); k++)
				g_draw->drawSegment(g_pathRaw[k - 1], g_pathRaw[k], 0.8f, ccColor4F{1.f, 0.f, 0.f, 1.f});
			for (size_t k = 1; k < g_pathBest.size(); k++)
				g_draw->drawSegment(g_pathBest[k - 1], g_pathBest[k], 0.8f, ccColor4F{0.f, 1.f, 0.2f, 1.f});
		}
		if (g_hud && g_hudDirty) {
			g_hudDirty = false;
			std::string text;
			for (size_t k = 0; k < g_hudLines.size(); k++) {
				if (k) text += "\n";
				text += g_hudLines[k];
			}
			g_hud->setString(text.c_str());
		}
	}

	void resetLevel() {
		if (!g_last.empty() && g_tick > 0) hudLog("RESET | ultima: " + g_last, false);
		PlayLayer::resetLevel();
		resetBuffer();
	}

	void onQuit() {
		resetBuffer();
		g_hud = nullptr;
		g_draw = nullptr;
		g_rings.clear();
		g_hazards.clear();
		g_solids.clear();
		g_slopes.clear();
		PlayLayer::onQuit();
	}
};

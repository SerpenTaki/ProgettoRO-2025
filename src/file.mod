set T ordered;
set K; 
set W;

param PVBoss;
param DK;
param DW;
param SKC;
param MWC;
param Smax;
param Mmax;
param Smin;
param Mmin;
param BigM := Smax;

var Stamina{T} >= 0;
var Mana{T} >= 0;
var DPT{T} >= 0;

var x{k in K, t in T} binary;  
var y{k in K, t in T} binary;  
var z{w in W, t in T} binary;  
var Boost{T} binary;
var u{T} binary;

var r{k in K, t in T} >= 0;    
var gamma{w in W, t in T} >= 0; 

minimize TurniMinimi:
    sum {t in T} t * u[t];

subject to StaminaMin {t in T: t != last(T)}: 
    Stamina[t] >= Smin;

subject to StaminaMax {t in T: t != last(T)}: 
    Stamina[t] <= Smax;

subject to ManaMin {t in T: t != last(T)}: 
    Mana[t] >= Mmin;

subject to ManaMax {t in T: t != last(T)}: 
    Mana[t] <= Mmax;

subject to Attacco2mani{k in K, t in T}:
    y[k,t] <= x[k,t];

subject to ConsumoStamina{t in T}:
    sum{k in K} SKC * (x[k,t] + (0.75 * y[k,t])) <= Stamina[t];

subject to ConsumoMana{t in T}:
    sum{w in W} z[w,t] * MWC <= Mana[t];

subject to AggiornaStamina{t in T: ord(t) < card(T)}:
    Stamina[t+1] = Stamina[t] - sum{k in K} SKC * (x[k,t] + (0.75 * y[k,t])) + 0.3 * sum{k in K} r[k,t];

subject to AggiornaMana{t in T: ord(t) < card(T)}:
    Mana[t+1] = Mana[t] - sum{w in W} z[w,t] * MWC + 0.2 * sum{w in W} gamma[w,t];

subject to RiposoCavaliere1 {k in K, t in T}:
    r[k,t] <= Smax * (1 - x[k,t]);

subject to RiposoCavaliere2 {k in K, t in T}:
    r[k,t] >= (Smax - Stamina[t]) - BigM * x[k,t];

subject to RiposoCavaliere3 {k in K, t in T}:
    r[k,t] <= Smax - Stamina[t];

subject to RiposoMago1 {w in W, t in T}:
    gamma[w,t] <= Mmax * (1 - z[w,t]);

subject to RiposoMago2 {w in W, t in T}:
    gamma[w,t] >= (Mmax - Mana[t]) - BigM * z[w,t];

subject to RiposoMago3 {w in W, t in T}:
    gamma[w,t] <= Mmax - Mana[t];

subject to BoostCondition {t in T: ord(t) > 2}:
    Boost[t] <= sum {w in W} (1 - z[w,t-1] + 1 - z[w,t-2]);
    
subject to BoostCondition2 {t in T: ord(t) > 2}:
	sum{w in W}(z[w,t-1]+z[w,t-2]) <= 1;

subject to UnoRiposaPerTurno {t in T}:
    sum {w in W} (1 - z[w,t]) <= 1;

subject to DannoPerTurno {t in T}:
    DPT[t] = sum{k in K} DK * (x[k,t] + y[k,t] + (0.2 * Boost[t])) + sum{w in W} z[w,t] * DW;

subject to BossSconfitto {t in T}:
    sum{tt in T: ord(tt) <= ord(t)} DPT[tt] >= PVBoss * u[t];

subject to SoloUnTurno:
    sum{t in T} u[t] = 1; 

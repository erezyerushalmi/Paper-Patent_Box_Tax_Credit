* Code Erez Yerushalmi, erez.yerushalmi@bcu.ac.uk
* 20 July 2026
* Paper title: Patent Boxes, Tax Credits, or Both?
* Authors: Michael Devereux, Ben Lockwood, Erez Yerushalmi
* ============================================================
* ============================================================
* Transfer Model: MCP/KKT formulation
* Full derivative version with A_l, A_e, B_l, B_e blocks
*
* Documentation: Paper_Online_Appendix.pdf.
* The common economic environment, government problem, MCP formulation, and
* regime definitions are in Section 2. The Transfer Model is in Section 4.
*
*
* Regime classification (Online Appendix, Section 2.4 and Table 1):
*       Regime 1 (tau interior, lam1 = 0):
*         1.1 = No instruments:       b ~ 0, c ~ 0
*         1.2 = PB only (interior):   0 < b < tau, c ~ 0
*         1.3 = PB exhausted:         b ~ tau, c ~ 0
*       Regime 2 (tau constrained, tau = taubar, lam1 > 0):
*         2.1 = No instruments:       b ~ 0, c ~ 0
*         2.2 = Credit only:          b ~ 0, c > 0
*         2.3 = PB interior, c = 0:   0 < b < tau, c ~ 0
*         2.4 = PB interior, c > 0:   0 < b < tau, c > 0
*         2.5 = PB exhausted, c = 0:  b ~ tau, c ~ 0
*         2.6 = PB exhausted, c > 0:  b ~ tau, c > 0
* The classification follows the common regime definitions used for both models.
* The Transfer Model-specific structure is documented in Online Appendix, Section 4.
*
* Core reduced-form logic (Online Appendix, Sections 4.1-4.4):
*
*       (tau,b,c) -> Dbig -> (p_l,p_e) -> (l,e) -> g -> sigma
*
* Code-to-appendix notation: Dbig is D, Nvar is N1, Lresp is l, Eresp is e,
* gResp is the composite innovation input r, and Sigma is sigma. The definitions
* of D, N1, p_l, and p_e are given in Online Appendix, Section 4.1.
*
* The firm side is solved analytically using the closed-form input demands in
* Online Appendix, Section 4.1. The MCP solves only the government KKT system
* described in Online Appendix, Sections 2.2-2.3.
*
* ============================================================
* scrdir="C:\GAMS_SCRATCH\"
* REMEMBER TO PLACE IN THE TERMINAL

Variables
    tau      "policy variable: corporate income tax rate"
    c        "policy variable: tax credit rate"
    b        "policy variable: patent box rate"
    Nvar     "effective labour-cost numerator Nl = 1-tau-c-0.5*theta*c^2"
    lam1     "KKT multiplier for tau <= taubar"
    lam2     "KKT multiplier for c <= 1-tau"
    lam3     "KKT multiplier for b <= tau"
;


Scalars
* ------------------------------------------------------------
* Deep / structural parameters (baseline values)
* ------------------------------------------------------------
    alpha       "innovation share parameter, 0<alpha<1"        / 0.6 /
    beta        "Nash bargaining weight, P=beta*DeltaInv"      / 0.5 /
    delta       "marginal cost of public funds"                / 1.2 /
    xi          "welfare treatment of manipulation costs"       / -1  /
    taubar      "upper bound on tau"                           / 0.8 /
    varepsilon  "demand elasticity parameter, >1"               / 5.0 /
    a_tech      "symmetric demand/technology shifter a"         / 5.0 /
    phi         "post-innovation marginal cost, phi<1"          / 0.7 /
    rho         "income-shifting parameter, d/P=rho*b"          / 0.8 /
    theta       "cost-shifting parameter, z/l=theta*c"          / 0.8 /
    epsN        "strictly positive lower bound for Nl"          / 1e-6 /

* ------------------------------------------------------------
* Calibration objects from the common real-side setup (Online Appendix, equations (1)-(10))
* ------------------------------------------------------------
    Zconst      "Z = eps^(-2eps)*(eps-1)^(2eps-1)"
    mMarkup     "m = eps/(eps-1)"
    piIUnder    "pre-innovation intermediate profit"
    piUnder     "pre-innovation total profit"
    DeltaInv    "Delta^I: innovation gain in intermediate profits"
    DeltaTot    "Delta: total innovation gain"
    P0          "arm's-length royalty P = beta*DeltaInv"

* ------------------------------------------------------------
* Reporting scalars for the Transfer Model objects in Online Appendix, Sections 4.1-4.4
* ------------------------------------------------------------
    DbigVal
    NVal
    plVal
    peVal
    lVal
    eVal
    gVal
    sigmaVal
    dVal
    zVal
    dOverPVal
    zOverLVal
    WVal
    dWdTauVal
    dWdCVal
    dWdBVal
    dsig_dgVal
    dg_dplVal
    dg_dpeVal
    dl_dplVal
    dl_dpeVal
    de_dplVal
    de_dpeVal
    dpl_dtauVal
    dpe_dtauVal
    dpl_dbVal
    dpe_dbVal
    dpl_dcVal
    dpe_dcVal
    MbVal
    McVal
    KbVal
    KcVal
    AlVal
    AeVal
    BlVal
    BeVal
    regimeVal   "regime: 1.1=none, 1.2=PB only, 1.3=PB exhausted; 2.1-2.6=constrained-tau sub-regimes"
    tolReg      "tolerance for near-zero / near-bound regime classification" / 1e-4 /
;


* ============================================================
* Initial calibration using the common real-side setup (Online Appendix, Section 2.1)
* ============================================================

abort$(alpha <= 0 or alpha >= 1)       "alpha must lie in (0,1).", alpha;
abort$(varepsilon <= 1)                "varepsilon must exceed 1.", varepsilon;
abort$(phi <= 0 or phi >= 1)           "phi must lie in (0,1).", phi;
abort$(taubar <= 0 or taubar > 1)      "taubar must lie in (0,1].", taubar;
abort$(beta <= 0 or beta >= 1)         "beta must lie in (0,1).", beta;
abort$(rho < 0 or theta < 0)           "rho and theta must be nonneg.", rho, theta;
abort$(xi < -1 or xi > delta - 1 + epsN)
                                       "xi must lie in [-1, delta-1].", xi, delta;

Zconst   = varepsilon**(-2*varepsilon) * (varepsilon - 1)**(2*varepsilon - 1);
mMarkup  = varepsilon/(varepsilon - 1);
piIUnder = Zconst * (a_tech**varepsilon);
piUnder  = (1 + mMarkup) * piIUnder;
DeltaInv = Zconst * (a_tech**varepsilon) * (phi**(1 - varepsilon) - 1);
DeltaTot = (1 + mMarkup) * DeltaInv;
P0       = beta * DeltaInv;

display Zconst, mMarkup, piIUnder, piUnder, DeltaInv, DeltaTot, P0;


* ============================================================
* Macros: reduced-form firm-response block (Online Appendix, Section 4.1)
* ============================================================

$macro P        (P0)
$macro Dbig        (DeltaInv*(1 - tau) + b*P + 0.5*P*rho*sqr(b))
$macro Nl       (Nvar)
$macro pl       (Nl/Dbig)
$macro pe       (1/Dbig)

$macro Lresp    ( alpha**((2-alpha)/2) * (1-alpha)**(-(1-alpha)/2) \
                * pl**(-(2-alpha)/2) * pe**((1-alpha)/2) )

$macro Eresp    ( alpha**(-alpha/2) * (1-alpha)**((1+alpha)/2) \
                * pl**(alpha/2) * pe**(-(1+alpha)/2) )

$macro gResp    ( alpha*log(Lresp) + (1-alpha)*log(Eresp) )
$macro Sigma    ( 1 - exp(-gResp) )


* ============================================================
* Macros: welfare shorthand (Online Appendix, Section 4.2)
* Mb = P(b+rho*b^2), Mc = c+theta*c^2, Kb = (P*rho*b^2)/2,
* and Kc = (theta*c^2)/2, matching the definitions in Section 4.2.
* ============================================================

$macro Mb       ( P*(b + rho*sqr(b)) )
$macro Mc       ( c + theta*sqr(c) )
$macro Kb       ( 0.5*P*rho*sqr(b) )
$macro Kc       ( 0.5*theta*sqr(c) )


* ============================================================
* Macros: minimal derivative set (Online Appendix, Section 4.3)
* ============================================================

$macro dsig_dg  (1 - Sigma)

$macro dg_dpl   (-alpha/(2*pl))
$macro dg_dpe   (-(1-alpha)/(2*pe))

$macro dl_dpl   (-(2-alpha)*Lresp/(2*pl))
$macro dl_dpe   ((1-alpha)*Lresp/(2*pe))

$macro de_dpl   (alpha*Eresp/(2*pl))
$macro de_dpe   (-(1+alpha)*Eresp/(2*pe))

$macro dpl_dtau ((pl*DeltaInv - 1)/Dbig)
$macro dpe_dtau ((pe*DeltaInv)/Dbig)

$macro dpl_db   (-(pl*P*(1 + rho*b))/Dbig)
$macro dpe_db   (-(pe*P*(1 + rho*b))/Dbig)

$macro dpl_dc   (-(1 + theta*c)/Dbig)
$macro dpe_dc   (0)


* ============================================================
* Macros: welfare derivative blocks (Online Appendix, Section 4.3)
* ============================================================

$macro Al       ( (tau*DeltaTot - Mb)*dsig_dg*dg_dpl - (tau + Mc)*dl_dpl )
$macro Ae       ( (tau*DeltaTot - Mb)*dsig_dg*dg_dpe - (tau + Mc)*dl_dpe )

$macro Bl       ( (DeltaTot + xi*Kb)*dsig_dg*dg_dpl + xi*Kc*dl_dpl \
                - (dl_dpl + de_dpl) )

$macro Be       ( (DeltaTot + xi*Kb)*dsig_dg*dg_dpe + xi*Kc*dl_dpe \
                - (dl_dpe + de_dpe) )


* ============================================================
* Macros: total welfare gradients (Online Appendix, Section 4.4)
* ============================================================

$macro dWdTau   ( (delta - 1)*(piUnder + DeltaTot*Sigma - Lresp) \
                + (delta - 1)*(Al*dpl_dtau + Ae*dpe_dtau) \
                + Bl*dpl_dtau + Be*dpe_dtau )

$macro dWdC     ( xi*theta*c*Lresp \
                + (delta - 1)*(-Lresp*(1 + 2*theta*c) + Al*dpl_dc) \
                + Bl*dpl_dc )

$macro dWdB     ( xi*Sigma*P*rho*b \
                + (delta - 1)*(-Sigma*P*(1 + 2*rho*b) + Al*dpl_db + Ae*dpe_db) \
                + Bl*dpl_db + Be*dpe_db )


* ============================================================
* Equations: KKT/MCP system (Online Appendix, equations (23)-(26))
* ============================================================

Equations
    Ftau    "stationarity wrt tau, paired with tau >= 0"
    Fc      "stationarity wrt c, paired with c >= 0"
    Fb      "stationarity wrt b, paired with b >= 0"
    DefN    "definition of Nvar = 1-tau-c-0.5*theta*c^2"
    G1      "taubar - tau >= 0, paired with lam1 >= 0"
    G2      "1 - tau - c >= 0, paired with lam2 >= 0"
    G3      "tau - b >= 0, paired with lam3 >= 0"
;

Ftau..  -dWdTau + lam1 + lam2 - lam3 =G= 0;
Fc..    -dWdC + lam2 =G= 0;
Fb..    -dWdB + lam3 =G= 0;
DefN..  Nvar =E= 1 - tau - c - 0.5*theta*sqr(c);
G1..    taubar - tau =G= 0;
G2..    1 - tau - c =G= 0;
G3..    tau - b =G= 0;


* ============================================================
* Bounds and baseline starting values
* Nvar.lo = epsN imposes the strict feasibility condition N1 > 0 required
* for positive effective input prices in Online Appendix, Section 4.1.
* ============================================================

tau.lo  = 0;   c.lo = 0;   b.lo = 0;   Nvar.lo = epsN;
lam1.lo = 0;   lam2.lo = 0;   lam3.lo = 0;

tau.l   = min(0.20, taubar/2);
c.l     = min(0.05, max(0, 1 - tau.l - 0.10));
b.l     = min(0.05, tau.l);
Nvar.l  = 1 - tau.l - c.l - 0.5*theta*sqr(c.l);

abort$(Nvar.l <= epsN) "Initial Nvar not positive.", Nvar.l, theta;

Model mTransNewFull /
    Ftau.tau, Fc.c, Fb.b, DefN.Nvar, G1.lam1, G2.lam2, G3.lam3
/;

* Baseline single solve for diagnostics
solve mTransNewFull using mcp;

display tau.l, c.l, b.l, lam1.l, lam2.l, lam3.l;


* $exit
* ============================================================
* TWO-DIMENSIONAL SENSITIVITY ANALYSIS
* ============================================================
*
* HOW TO USE:
*   1. Set baseline parameter values in the Scalars block above.
*   2. Choose the OUTER loop parameter: set outerPar below.
*   3. Choose the INNER loop parameter: set innerPar below.
*   4. Each produces its own grid; sizes are set automatically
*      per-parameter using the same ranges as v6, now applied
*      to both axes independently.
*   5. Choose xiMode (1 = resource cost, 2 = transfer/fines).
*   6. Run. Output: res_2d(outerSet, innerSet, *).
*      Excel sheet is named after the outer parameter.
*
* PARAMETER MENU (activate exactly one line for each of outerPar and innerPar):
*
*   rho        0.0 to 0.8 (9 steps of 0.1)
*   theta      0.0 to 0.8 (9 steps of 0.1)
*   delta      1.0 to 1.8 (9 steps of 0.1)
*   alpha      0.1 to 0.9 (9 steps of 0.1)
*   beta       0.1 to 0.9 (9 steps of 0.1)
*   phi        0.1 to 0.9 (9 steps of 0.1)
*   taubar     0.1 to 0.9 (9 steps of 0.1)
*   varepsilon 1.5 to 5.5 (9 steps of 0.5)
*   a_tech     1.0 to 9.0 (9 steps of 1.0)
*
* ============================================================

Set parName /
    rho
    theta
    delta
    alpha
    beta
    phi
    varepsilon
    a_tech
    taubar
/;

* ============================================================
* USER CHOICE: select outer and inner loop parameters
* (uncomment exactly ONE line in each block)
* ============================================================

**** OUTER parameter (y-axis of regime map) ****
Set outerPar(parName) /
   rho
*   theta
*   delta
*   alpha
*   beta
*    phi
*   varepsilon
*   a_tech
*   taubar
/;

**** INNER parameter (x-axis of regime map) ****
Set innerPar(parName) /
*   rho
   theta
*   delta
*   alpha
*   beta
*   phi
*   varepsilon
*   a_tech
*    taubar
/;

* ============================================================
* Welfare treatment of shifting costs, xi (Online Appendix, Section 4.2)
*   xiMode = 1: real resource cost,  xi = -1
*   xiMode = 2: transfer/fines case, xi = delta - 1
* ============================================================
Scalar xiMode / 1 /;

* ============================================================
* Grid index sets (9 points each axis)
* ============================================================
Set outerSet / o1*o9 /;
Set innerSet / i1*i9 /;

* ============================================================
* Grid value arrays and baseline store
* ============================================================
Parameter outerVal(outerSet) "grid values for outer parameter";
Parameter innerVal(innerSet) "grid values for inner parameter";
Parameter baseVal(parName)   "baseline deep parameter values";

* Store baseline
baseVal('rho')        = rho;
baseVal('theta')      = theta;
baseVal('delta')      = delta;
baseVal('alpha')      = alpha;
baseVal('beta')       = beta;
baseVal('phi')        = phi;
baseVal('varepsilon') = varepsilon;
baseVal('a_tech')     = a_tech;
baseVal('taubar')     = taubar;

* ============================================================
* Populate outer and inner grid values for the sensitivity analysis
* The ranges below are user-selected numerical grids and are not model equations.
* ============================================================

outerVal(outerSet) = 0;
if(outerPar('alpha') or outerPar('beta') or outerPar('phi') or outerPar('taubar'),
   outerVal(outerSet) = 0.1 + 0.1*(ord(outerSet) - 1);
);
if(outerPar('rho') or outerPar('theta'),
*   outerVal(outerSet) = 0.0 + 0.1*(ord(outerSet) - 1);
   outerVal(outerSet) = 0.0 + 1*(ord(outerSet) - 1);
);
if(outerPar('delta'),
   outerVal(outerSet) = 1.0000001 + 0.1*(ord(outerSet) - 1);
);
if(outerPar('varepsilon'),
   outerVal(outerSet) = 1.5 + 0.5*(ord(outerSet) - 1);
);
if(outerPar('a_tech'),
   outerVal(outerSet) = 1.0 + 1.0*(ord(outerSet) - 1);
);

innerVal(innerSet) = 0;
if(innerPar('alpha') or innerPar('beta') or innerPar('phi') or innerPar('taubar'),
   innerVal(innerSet) = 0.1 + 0.1*(ord(innerSet) - 1);
);
if(innerPar('rho') or innerPar('theta'),
*   innerVal(innerSet) = 0.0 + 0.1*(ord(innerSet) - 1);
   innerVal(innerSet) = 0.0 + 2*(ord(innerSet) - 1);
);
if(innerPar('delta'),
   innerVal(innerSet) = 1.0000001 + 0.1*(ord(innerSet) - 1);
);
if(innerPar('varepsilon'),
   innerVal(innerSet) = 1.5 + 0.5*(ord(innerSet) - 1);
);
if(innerPar('a_tech'),
   innerVal(innerSet) = 1.0 + 1.0*(ord(innerSet) - 1);
);

display outerPar, innerPar, outerVal, innerVal;

* ============================================================
* Abort if outer and inner are the same parameter
* ============================================================
abort$(sum(parName$(outerPar(parName) and innerPar(parName)), 1) > 0)
    "outerPar and innerPar must be different parameters.";

* ============================================================
* Output array: (outerSet x innerSet x columns)
* ============================================================
Parameter res_2d(outerSet, innerSet, *);
option clear = res_2d;

* ============================================================
* Apply xiMode to baseline before the loop
* ============================================================
if(xiMode = 1,   xi = -1;         );
if(xiMode = 2,   xi = delta - 1;  );

abort$(xi < -1 or xi > delta - 1 + epsN)
    "xi out of range at baseline.", xi, delta;

* ============================================================
* Double loop
* ============================================================
loop(outerSet,

* --- Set outer parameter value ---
    rho        = baseVal('rho');
    theta      = baseVal('theta');
    delta      = baseVal('delta');
    alpha      = baseVal('alpha');
    beta       = baseVal('beta');
    phi        = baseVal('phi');
    varepsilon = baseVal('varepsilon');
    a_tech     = baseVal('a_tech');
    taubar     = baseVal('taubar');

    if(outerPar('rho'),        rho        = outerVal(outerSet));
    if(outerPar('theta'),      theta      = outerVal(outerSet));
    if(outerPar('delta'),      delta      = outerVal(outerSet));
    if(outerPar('alpha'),      alpha      = outerVal(outerSet));
    if(outerPar('beta'),       beta       = outerVal(outerSet));
    if(outerPar('phi'),        phi        = outerVal(outerSet));
    if(outerPar('varepsilon'), varepsilon = outerVal(outerSet));
    if(outerPar('a_tech'),     a_tech     = outerVal(outerSet));
    if(outerPar('taubar'),     taubar     = outerVal(outerSet));

    if(xiMode = 1,   xi = -1;         );
    if(xiMode = 2,   xi = delta - 1;  );

* --- Inner loop ---
    loop(innerSet,

*   Reset to outer-layer values before applying inner parameter
        rho        = baseVal('rho');
        theta      = baseVal('theta');
        delta      = baseVal('delta');
        alpha      = baseVal('alpha');
        beta       = baseVal('beta');
        phi        = baseVal('phi');
        varepsilon = baseVal('varepsilon');
        a_tech     = baseVal('a_tech');
        taubar     = baseVal('taubar');

*   Re-apply outer parameter (so inner does not clobber it)
        if(outerPar('rho'),        rho        = outerVal(outerSet));
        if(outerPar('theta'),      theta      = outerVal(outerSet));
        if(outerPar('delta'),      delta      = outerVal(outerSet));
        if(outerPar('alpha'),      alpha      = outerVal(outerSet));
        if(outerPar('beta'),       beta       = outerVal(outerSet));
        if(outerPar('phi'),        phi        = outerVal(outerSet));
        if(outerPar('varepsilon'), varepsilon = outerVal(outerSet));
        if(outerPar('a_tech'),     a_tech     = outerVal(outerSet));
        if(outerPar('taubar'),     taubar     = outerVal(outerSet));

*   Apply inner parameter
        if(innerPar('rho'),        rho        = innerVal(innerSet));
        if(innerPar('theta'),      theta      = innerVal(innerSet));
        if(innerPar('delta'),      delta      = innerVal(innerSet));
        if(innerPar('alpha'),      alpha      = innerVal(innerSet));
        if(innerPar('beta'),       beta       = innerVal(innerSet));
        if(innerPar('phi'),        phi        = innerVal(innerSet));
        if(innerPar('varepsilon'), varepsilon = innerVal(innerSet));
        if(innerPar('a_tech'),     a_tech     = innerVal(innerSet));
        if(innerPar('taubar'),     taubar     = innerVal(innerSet));

*   Re-apply xi rule (must follow delta in case delta changed)
        if(xiMode = 1,   xi = -1;         );
        if(xiMode = 2,   xi = delta - 1;  );

*   Admissibility checks (skip inadmissible cells, store -999)
        if(alpha <= 0 or alpha >= 1
        or varepsilon <= 1
        or phi <= 0 or phi >= 1
        or taubar <= 0 or taubar > 1
        or beta <= 0 or beta >= 1
        or rho < 0 or theta < 0
        or xi < -1 or xi > delta - 1 + epsN,

            res_2d(outerSet,innerSet,'feasible') = 0;
            res_2d(outerSet,innerSet,'regime')   = -999;

        else

*       Recalibrate derived objects
            Zconst   = varepsilon**(-2*varepsilon) * (varepsilon-1)**(2*varepsilon-1);
            mMarkup  = varepsilon/(varepsilon - 1);
            piIUnder = Zconst * (a_tech**varepsilon);
            piUnder  = (1 + mMarkup) * piIUnder;
            DeltaInv = Zconst * (a_tech**varepsilon) * (phi**(1-varepsilon) - 1);
            DeltaTot = (1 + mMarkup) * DeltaInv;
            P0       = beta * DeltaInv;

*       Starting values (conservative, keep Nvar positive)
            tau.l   = min(0.20, taubar/2);
            c.l     = min(0.05, max(0, 1 - tau.l - 0.10));
            b.l     = min(0.05, tau.l);
            Nvar.l  = 1 - tau.l - c.l - 0.5*theta*sqr(c.l);

            if(Nvar.l <= epsN,
               c.l    = 0;
               Nvar.l = 1 - tau.l;
            );

            lam1.l = 0;   lam2.l = 0;   lam3.l = 0;

            solve mTransNewFull using mcp;

*       Post-solve reporting
            DbigVal   = DeltaInv*(1-tau.l) + b.l*P0 + 0.5*P0*rho*sqr(b.l);
            NVal      = Nvar.l;
            plVal     = NVal/DbigVal;
            peVal     = 1/DbigVal;

            lVal      = alpha**((2-alpha)/2) * (1-alpha)**(-(1-alpha)/2)
                      * plVal**(-(2-alpha)/2) * peVal**((1-alpha)/2);
            eVal      = alpha**(-alpha/2) * (1-alpha)**((1+alpha)/2)
                      * plVal**(alpha/2) * peVal**(-(1+alpha)/2);

            gVal      = alpha*log(lVal) + (1-alpha)*log(eVal);
            sigmaVal  = 1 - exp(-gVal);
            dVal      = P0*rho*b.l;
            zVal      = lVal*theta*c.l;
            dOverPVal = rho*b.l;
            zOverLVal = theta*c.l;

            WVal = piUnder + DeltaTot*sigmaVal - (lVal + eVal)
                 + xi*( sigmaVal*0.5*P0*rho*sqr(b.l) + 0.5*theta*sqr(c.l)*lVal )
                 + (delta-1)*( tau.l*(piUnder + DeltaTot*sigmaVal - lVal)
                             - sigmaVal*P0*(b.l + rho*sqr(b.l))
                             - (c.l + theta*sqr(c.l))*lVal );

            MbVal  = P0*(b.l + rho*sqr(b.l));
            McVal  = c.l + theta*sqr(c.l);
            KbVal  = 0.5*P0*rho*sqr(b.l);
            KcVal  = 0.5*theta*sqr(c.l);

            dsig_dgVal = 1 - sigmaVal;
            dg_dplVal  = -alpha/(2*plVal);
            dg_dpeVal  = -(1-alpha)/(2*peVal);

            dl_dplVal  = -(2-alpha)*lVal/(2*plVal);
            dl_dpeVal  = (1-alpha)*lVal/(2*peVal);
            de_dplVal  = alpha*eVal/(2*plVal);
            de_dpeVal  = -(1+alpha)*eVal/(2*peVal);

            dpl_dtauVal = (plVal*DeltaInv - 1)/DbigVal;
            dpe_dtauVal = (peVal*DeltaInv)/DbigVal;
            dpl_dbVal   = -(plVal*P0*(1+rho*b.l))/DbigVal;
            dpe_dbVal   = -(peVal*P0*(1+rho*b.l))/DbigVal;
            dpl_dcVal   = -(1+theta*c.l)/DbigVal;
            dpe_dcVal   = 0;

            AlVal = (tau.l*DeltaTot - MbVal)*dsig_dgVal*dg_dplVal
                  - (tau.l + McVal)*dl_dplVal;
            AeVal = (tau.l*DeltaTot - MbVal)*dsig_dgVal*dg_dpeVal
                  - (tau.l + McVal)*dl_dpeVal;
            BlVal = (DeltaTot + xi*KbVal)*dsig_dgVal*dg_dplVal
                  + xi*KcVal*dl_dplVal - (dl_dplVal + de_dplVal);
            BeVal = (DeltaTot + xi*KbVal)*dsig_dgVal*dg_dpeVal
                  + xi*KcVal*dl_dpeVal - (dl_dpeVal + de_dpeVal);

            dWdTauVal = (delta-1)*(piUnder + DeltaTot*sigmaVal - lVal)
                      + (delta-1)*(AlVal*dpl_dtauVal + AeVal*dpe_dtauVal)
                      + BlVal*dpl_dtauVal + BeVal*dpe_dtauVal;

            dWdCVal   = xi*theta*c.l*lVal
                      + (delta-1)*(-lVal*(1+2*theta*c.l) + AlVal*dpl_dcVal)
                      + BlVal*dpl_dcVal;

            dWdBVal   = xi*sigmaVal*P0*rho*b.l
                      + (delta-1)*(-sigmaVal*P0*(1+2*rho*b.l)
                                  + AlVal*dpl_dbVal + AeVal*dpe_dbVal)
                      + BlVal*dpl_dbVal + BeVal*dpe_dbVal;

* -----------------------------------------------------------------
*   REGIME CLASSIFICATION  (Online Appendix Sections 1.3 and 1.4)
*   Two top-level regimes, determined by whether tau is interior
*   or constrained at its upper bound taubar.
*
*   Regime 1 — tau interior (lam1 = 0, 0 < tau < taubar):
*     1.1 = No instruments:        b ~ 0, c ~ 0
*     1.2 = PB only (interior):    0 < b < tau, c ~ 0
*     1.3 = PB exhausted:          b ~ tau, c ~ 0
*           (KKT: dW/dtau + dW/db = 0, lam3 >= 0, dW/dc <= 0)
*
*   Regime 2 — tau constrained (tau = taubar, lam1 > 0):
*     2.1 = No instruments:        b ~ 0, c ~ 0
*     2.2 = Credit only:           b ~ 0, c > 0
*     2.3 = PB interior, c = 0:   0 < b < tau, c ~ 0
*     2.4 = PB interior, c > 0:   0 < b < tau, c > 0
*     2.5 = PB exhausted, c = 0:  b ~ tau, c ~ 0
*     2.6 = PB exhausted, c > 0:  b ~ tau, c > 0
*
*   Tolerance: tolReg = 1e-4
* -----------------------------------------------------------------
            regimeVal = 0;
            if(lam1.l > tolReg or abs(tau.l - taubar) < tolReg,
*               --- Regime 2: tau constrained ---
                if(b.l < tolReg and c.l < tolReg,
                    regimeVal = 2.1;
                elseif b.l < tolReg and c.l > tolReg,
                    regimeVal = 2.2;
                elseif abs(b.l - tau.l) < tolReg and c.l < tolReg,
                    regimeVal = 2.5;
                elseif abs(b.l - tau.l) < tolReg and c.l > tolReg,
                    regimeVal = 2.6;
                elseif b.l > tolReg and c.l < tolReg,
                    regimeVal = 2.3;
                else
                    regimeVal = 2.4;
                );
            else
*               --- Regime 1: tau interior ---
                if(b.l < tolReg and c.l < tolReg,
                    regimeVal = 1.1;
                elseif abs(b.l - tau.l) < tolReg,
                    regimeVal = 1.3;
                else
                    regimeVal = 1.2;
                );
            );

*       Store results
            res_2d(outerSet,innerSet,'feasible')   = 1;
            res_2d(outerSet,innerSet,'outerVal')   = outerVal(outerSet);
            res_2d(outerSet,innerSet,'innerVal')   = innerVal(innerSet);

            res_2d(outerSet,innerSet,'rho')        = rho + 1e-12;
            res_2d(outerSet,innerSet,'theta')      = theta + 1e-12;
            res_2d(outerSet,innerSet,'delta')      = delta;
            res_2d(outerSet,innerSet,'alpha')      = alpha;
            res_2d(outerSet,innerSet,'beta')       = beta;
            res_2d(outerSet,innerSet,'phi')        = phi;
            res_2d(outerSet,innerSet,'varepsilon') = varepsilon;
            res_2d(outerSet,innerSet,'a_tech')     = a_tech;
            res_2d(outerSet,innerSet,'xi')         = xi;
            res_2d(outerSet,innerSet,'taubar')     = taubar + 1e-12;

            res_2d(outerSet,innerSet,'DeltaInv')   = DeltaInv;
            res_2d(outerSet,innerSet,'DeltaTot')   = DeltaTot;
            res_2d(outerSet,innerSet,'P0')         = P0 + 1e-12;

            res_2d(outerSet,innerSet,'tau')        = tau.l + 1e-12;
            res_2d(outerSet,innerSet,'c')          = c.l   + 1e-12;
            res_2d(outerSet,innerSet,'b')          = b.l   + 1e-12;
            res_2d(outerSet,innerSet,'N')          = NVal;
            res_2d(outerSet,innerSet,'Dbig')       = DbigVal;
            res_2d(outerSet,innerSet,'pl')         = plVal;
            res_2d(outerSet,innerSet,'pe')         = peVal;
            res_2d(outerSet,innerSet,'l')          = lVal;
            res_2d(outerSet,innerSet,'e')          = eVal;
            res_2d(outerSet,innerSet,'g')          = gVal;
            res_2d(outerSet,innerSet,'sigma')      = sigmaVal + 1e-12;
            res_2d(outerSet,innerSet,'d/P')        = dOverPVal + 1e-12;
            res_2d(outerSet,innerSet,'z/l')        = zOverLVal + 1e-12;
            res_2d(outerSet,innerSet,'W')          = WVal;

            res_2d(outerSet,innerSet,'dWdTau')     = dWdTauVal;
            res_2d(outerSet,innerSet,'dWdC')       = dWdCVal;
            res_2d(outerSet,innerSet,'dWdB')       = dWdBVal;

            res_2d(outerSet,innerSet,'lam1')       = lam1.l + 1e-12;
            res_2d(outerSet,innerSet,'lam2')       = lam2.l + 1e-12;
            res_2d(outerSet,innerSet,'lam3')       = lam3.l + 1e-12;

            res_2d(outerSet,innerSet,'regime')     = regimeVal;

        );

    );

);


* ============================================================
* Display and export
* ============================================================

display res_2d;

* Export: file name encodes xi mode and outer/inner parameter names.
* The Excel sheet is always named RES for gdxxrw compatibility.
* The outer parameter label appears in the filename so you can
* run multiple configurations without overwriting output.

if(xiMode = 1,
    execute_unload "res_TM_v8_xi1.gdx", res_2d;
    execute 'gdxxrw.exe res_TM_v8_xi1.gdx O=res_TM_v8_xi1.xlsx par=res_2d rng=RES!A2';
    execute 'xlstalk.exe -O res_TM_v8_xi1.xlsx';
);

if(xiMode = 2,
    execute_unload "res_TM_v8_xidelta.gdx", res_2d;
    execute 'gdxxrw.exe res_TM_v8_xidelta.gdx O=res_TM_v8_xidelta.xlsx par=res_2d rng=RES!A2';
    execute 'xlstalk.exe -O res_TM_v8_xidelta.xlsx';
);


* ============================================================
* End of file
* ============================================================

* Code Erez Yerushalmi, erez.yerushalmi@bcu.ac.uk
* 18 May 2026
* Paper title: Patent Boxes, Tax Credits, or Both?
* Authors: Michael Devereux, Ben Lockwood, Erez Yerushalmi
* ============================================================
* Main Model: MCP/KKT formulation
* Full derivative version with A_l, A_e, B_l, B_e blocks
*
* Documentation: Paper_Online_Appendix.pdf.
* The common calibration, government problem, MCP formulation, and regime
* definitions are in Section 2; the Main Model is documented in Section 3.
*
*
* Core reduced-form logic (Online Appendix, Sections 3.1-3.4):
*
*       (tau,b,c) -> (N,Dbig) -> (p_l,p_e) -> (l,e) -> r -> sigma
*
* r is the composite innovation input in the Online Appendix.
* Online Appendix, equations (28)-(30),
*
*       Dbig = 1 - tau + b,
*       N    = 1 - tau - c,
*       p_l  = N/Dbig,
*       p_e  = 1/Dbig.
*
* The firm side is solved analytically using the closed-form
* input demand system. The MCP solves only the government KKT.
*
*
* ============================================================
* scrdir="C:\GAMS_SCRATCH\"
* REMEMBER TO PLACE IN THE TERMINAL IF NEEDED

Variables
    tau       "policy variable: corporate income tax rate"
    c         "policy variable: tax credit rate"
    b         "policy variable: patent box rate"
    Nvar      "effective labour-cost numerator N = 1-tau-c"
    DbigVar   "effective innovation-return denominator Dbig = 1-tau+b"
    lam1      "KKT multiplier for tau <= taubar"
    lam2      "KKT multiplier for c <= 1-tau"
    lam3      "KKT multiplier for b <= tau"
;

Scalars
* ------------------------------------------------------------
* Deep / structural parameters (baseline values)
* ------------------------------------------------------------
    alpha       "innovation share parameter, 0<alpha<1"        / 0.8 /
    beta        "Nash bargaining weight, P=beta*DeltaInv"      / 0.5 /
    delta       "marginal cost of public funds"                / 1.2 /
    taubar      "upper bound on tau"                           / 0.8 /
    varepsilon  "demand elasticity parameter, >1"               / 5.0 /
    a_tech      "symmetric demand/technology shifter a"         / 5.0 /
    phi         "post-innovation marginal cost, phi<1"          / 0.7 /
    epsN        "strictly positive lower bound for N and Dbig"  / 1e-6 /

* ------------------------------------------------------------
* Calibration objects shared by Main Model and Transfer Model  (Online Appendix, equations (1)-(10))
* ------------------------------------------------------------
    Zconst      "Z = eps^(-2eps)*(eps-1)^(2eps-1)"
    mMarkup     "m = eps/(eps-1)"
    piIUnder    "pre-innovation intermediate profit"
    piUnder     "pre-innovation total profit"
    DeltaInv    "Delta^I: innovation gain in intermediate profits"
    DeltaF      "Delta^F: innovation gain in final-good profits"
    DeltaTot    "Delta: total innovation gain"
    P0          "arm's-length royalty P = beta*DeltaInv"

* ------------------------------------------------------------
* Main Model firm-response scaling constants (Online Appendix, equations (34)-(37))
* These encode the (beta*DeltaInv)^{+/-1/2} factor in the Main Model firm FOC.
* Recomputed every time alpha, beta, or DeltaInv changes.
* ------------------------------------------------------------
    B_sigma     "scaling constant for sigma: (beta*DeltaInv)^{-1/2} * alpha^{-alpha/2} * (1-alpha)^{(alpha-1)/2}"
    B_l         "scaling constant for l:     (beta*DeltaInv)^{+1/2} * alpha^{(2-alpha)/2} * (1-alpha)^{(alpha-1)/2}"
    B_epsilon   "scaling constant for e:     (beta*DeltaInv)^{+1/2} * alpha^{-alpha/2} * (1-alpha)^{(1+alpha)/2}"

* ------------------------------------------------------------
* Reporting scalars (post-solve diagnostics)
* ------------------------------------------------------------
    DbigVal
    NVal
    plVal
    peVal
    lVal
    eVal
    gVal
    sigmaVal
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
    AlVal
    AeVal
    BlVal
    BeVal
* Note: the declaration text below is retained unchanged as model code.
* Regimes 1.1-1.3 are tau interior;
* Regimes 2.1-2.6 are the constrained-tau subregimes (Online Appendix, Table 1).
    regimeVal   "regime classification: 1.1=none, 1.2=PB only, 1.3=PB exhausted+TC, 2=constrained-tau and sub-categories"
    tolReg      "tolerance for near-zero / near-bound regime classification" / 1e-4 /
;


* ============================================================
* Initial calibration (baseline solve only)  (Online Appendix, Section 2.1)
* ============================================================

abort$(alpha <= 0 or alpha >= 1)       "alpha must lie in (0,1).", alpha;
abort$(varepsilon <= 1)                "varepsilon must exceed 1.", varepsilon;
abort$(phi <= 0 or phi >= 1)           "phi must lie in (0,1).", phi;
abort$(taubar <= 0 or taubar > 1)      "taubar must lie in (0,1].", taubar;
abort$(beta <= 0 or beta >= 1)         "beta must lie in (0,1).", beta;
abort$(delta < 1)                      "delta must be at least 1.", delta;

Zconst   = varepsilon**(-2*varepsilon) * (varepsilon - 1)**(2*varepsilon - 1);
mMarkup  = varepsilon/(varepsilon - 1);
piIUnder = Zconst * (a_tech**varepsilon);
piUnder  = (1 + mMarkup) * piIUnder;
DeltaInv = Zconst * (a_tech**varepsilon) * (phi**(1 - varepsilon) - 1);
DeltaF   = mMarkup * DeltaInv;
DeltaTot = (1 + mMarkup) * DeltaInv;
P0       = beta * DeltaInv;

abort$(DeltaInv <= epsN) "DeltaInv must be positive and non-negligible.", DeltaInv;

* Compute Main Model scaling constants (Online Appendix, equations (34)-(37))
B_sigma   = (DeltaInv*beta)**(-0.5) * alpha**(-alpha/2)       * (1 - alpha)**((alpha - 1)/2);
B_l       = (DeltaInv*beta)**( 0.5) * alpha**((2 - alpha)/2)  * (1 - alpha)**((alpha - 1)/2);
B_epsilon = (DeltaInv*beta)**( 0.5) * alpha**(-alpha/2)       * (1 - alpha)**((1 + alpha)/2);

display Zconst, mMarkup, piIUnder, piUnder, DeltaInv, DeltaF, DeltaTot, P0;
display B_sigma, B_l, B_epsilon;


* ============================================================
* Macros: reduced-form firm-response block  (Main Model)
*
* Main Model closed-form responses (Online Appendix, equations (34), (35), and (37)):
*   l     = Dbig^{1/2} * N^{(alpha-2)/2} * B_l
*   e     = Dbig^{1/2} * N^{alpha/2}     * B_epsilon
*   sigma = 1 - Dbig^{-1/2} * N^{alpha/2} * B_sigma
*
* The B constants absorb (beta*DeltaInv)^{+/-1/2} and are
* recomputed each loop iteration when beta or DeltaInv changes.
* ============================================================

$macro P        (P0)
$macro Dbig     (DbigVar)
$macro Nl       (Nvar)
$macro pl       (Nl/Dbig)
$macro pe       (1/Dbig)

$macro Lresp    ( Dbig**0.5 * Nl**((alpha - 2)/2) * B_l )

$macro Eresp    ( Dbig**0.5 * Nl**(alpha/2)       * B_epsilon )

$macro Sigma    ( 1 - Dbig**(-0.5) * Nl**(alpha/2) * B_sigma )


* ============================================================
* Macros: welfare shorthand for the Main Model
* ============================================================
*
* Main Model welfare per firm (Online Appendix, equation (39)):
*
* W = piUnder + DeltaTot*Sigma - Lresp - Eresp
*     + (delta-1)*( tau*(piUnder + DeltaTot*Sigma - Lresp)
*                   - b*P*Sigma - c*Lresp )
*
* Equivalently (Online Appendix, equation (40)):
*
* W = piUnder*(1 + tau*(delta-1))
*     + [(1+(delta-1)*tau)*DeltaTot - (delta-1)*b*P]*Sigma
*     - [1+(delta-1)*(tau+c)]*Lresp
*     - Eresp.
*

$macro Acoef    ( (1 + (delta - 1)*tau)*DeltaTot - (delta - 1)*b*P )
$macro Bcoef    ( 1 + (delta - 1)*(tau + c) )

* ============================================================
* Macros: minimal derivative set
* ============================================================
*
* The partial derivatives of l, e, r, sigma with respect to
* p_l and p_e are derived from the firm FOC.  They hold for
* any l, e that satisfy the Main Model first-order conditions,
* regardless of the B-constant normalisation (the B factor
* cancels in every ratio l/p_l, e/p_e, etc.).
*
* See Online Appendix, equations (43)-(45).
*

$macro dsig_dg  (1 - Sigma)

$macro dg_dpl   (-alpha/(2*pl))
$macro dg_dpe   (-(1-alpha)/(2*pe))

$macro dl_dpl   (-(2-alpha)*Lresp/(2*pl))
$macro dl_dpe   ((1-alpha)*Lresp/(2*pe))

$macro de_dpl   (alpha*Eresp/(2*pl))
$macro de_dpe   (-(1+alpha)*Eresp/(2*pe))

* Main Model input-price derivatives (Online Appendix, equations (41)-(42)):
*   p_l = (1-tau-c)/(1-tau+b) = N/Dbig
*   p_e = 1/(1-tau+b) = 1/Dbig
$macro dpl_dtau (-(b + c)/sqr(Dbig))
$macro dpe_dtau (1/sqr(Dbig))

$macro dpl_db   (-(1 - tau - c)/sqr(Dbig))
$macro dpe_db   (-1/sqr(Dbig))

$macro dpl_dc   (-1/Dbig)
$macro dpe_dc   (0)


* ============================================================
* Macros: welfare derivative blocks
* ============================================================
*
* A_l, A_e are the effects of p_l, p_e on the tax-revenue block.
* B_l, B_e are the effects of p_l, p_e on the non-tax welfare block.
*
* With symmetry, n=1, and no spillovers, the Online Appendix blocks
* in equations (46)-(49) reduce to:
*
*   A_l = (tau*Delta - b*P)*sigma_g*g_pl - (tau+c)*l_pl
*   A_e = (tau*Delta - b*P)*sigma_g*g_pe - (tau+c)*l_pe
*   B_l = Delta*sigma_g*g_pl - (l_pl+e_pl)
*   B_e = Delta*sigma_g*g_pe - (l_pe+e_pe)
*

$macro Al       ( (tau*DeltaTot - b*P)*dsig_dg*dg_dpl - (tau + c)*dl_dpl )
$macro Ae       ( (tau*DeltaTot - b*P)*dsig_dg*dg_dpe - (tau + c)*dl_dpe )

$macro Bl       ( DeltaTot*dsig_dg*dg_dpl - (dl_dpl + de_dpl) )
$macro Be       ( DeltaTot*dsig_dg*dg_dpe - (dl_dpe + de_dpe) )


* ============================================================
* Macros: total welfare gradients (Online Appendix, equations (54)-(56))
* ============================================================

$macro dWdTau   ( (delta - 1)*(piUnder + DeltaTot*Sigma - Lresp) \
                + (delta - 1)*(Al*dpl_dtau + Ae*dpe_dtau) \
                + Bl*dpl_dtau + Be*dpe_dtau )

$macro dWdC     ( (delta - 1)*(-Lresp + Al*dpl_dc) \
                + Bl*dpl_dc )

$macro dWdB     ( (delta - 1)*(-Sigma*P + Al*dpl_db + Ae*dpe_db) \
                + Bl*dpl_db + Be*dpe_db )


* ============================================================
* Equations: KKT/MCP system (Online Appendix, equations (23)-(26))
* ============================================================

Equations
    Ftau    "stationarity wrt tau, paired with tau >= 0"
    Fc      "stationarity wrt c, paired with c >= 0"
    Fb      "stationarity wrt b, paired with b >= 0"
    DefN    "definition of Nvar = 1-tau-c"
    DefD    "definition of DbigVar = 1-tau+b"
    G1      "taubar - tau >= 0, paired with lam1 >= 0"
    G2      "1 - tau - c >= 0, paired with lam2 >= 0"
    G3      "tau - b >= 0, paired with lam3 >= 0"
;

Ftau..  -dWdTau + lam1 + lam2 - lam3 =G= 0;
Fc..    -dWdC + lam2                 =G= 0;
Fb..    -dWdB + lam3                 =G= 0;
DefN..  Nvar                         =E= 1 - tau - c;
DefD..  DbigVar                      =E= 1 - tau + b;
G1..    taubar - tau                 =G= 0;
G2..    1 - tau - c                  =G= 0;
G3..    tau - b                      =G= 0;


* ============================================================
* Bounds and baseline starting values
* ============================================================

tau.lo  = 0;   c.lo = 0;   b.lo = 0;   Nvar.lo = epsN;   DbigVar.lo = epsN;
lam1.lo = 0;   lam2.lo = 0;   lam3.lo = 0;

tau.l     = min(0.20, taubar/2);
c.l       = min(0.05, max(0, 1 - tau.l - 0.10));
b.l       = min(0.05, tau.l);
Nvar.l    = 1 - tau.l - c.l;
DbigVar.l = 1 - tau.l + b.l;

abort$(Nvar.l <= epsN)    "Initial Nvar not positive.", Nvar.l;
abort$(DbigVar.l <= epsN) "Initial DbigVar not positive.", DbigVar.l;

Model mMainNewFull /
    Ftau.tau, Fc.c, Fb.b, DefN.Nvar, DefD.DbigVar, G1.lam1, G2.lam2, G3.lam3
/;

* Baseline single solve for diagnostics
solve mMainNewFull using mcp;

display tau.l, c.l, b.l, Nvar.l, DbigVar.l, lam1.l, lam2.l, lam3.l;

* Post-solve diagnostics for baseline
DbigVal  = DbigVar.l;
NVal     = Nvar.l;
plVal    = NVal/DbigVal;
peVal    = 1/DbigVal;

lVal     = DbigVal**0.5 * NVal**((alpha - 2)/2) * B_l;
eVal     = DbigVal**0.5 * NVal**(alpha/2)       * B_epsilon;
gVal     = alpha*log(lVal) + (1-alpha)*log(eVal);
sigmaVal = 1 - DbigVal**(-0.5) * NVal**(alpha/2) * B_sigma;

WVal = piUnder + DeltaTot*sigmaVal - lVal - eVal
     + (delta-1)*( tau.l*(piUnder + DeltaTot*sigmaVal - lVal)
                 - b.l*P0*sigmaVal
                 - c.l*lVal );

display lVal, eVal, gVal, sigmaVal, WVal;


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
*      per-parameter.
*   5. Run. Output: res_2d(outerSet, innerSet, *).
*
* PARAMETER MENU (activate exactly one line for each of outerPar and innerPar):
*
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
   delta
*   alpha
*   beta
*   phi
*   varepsilon
*   a_tech
*   taubar
/;

**** INNER parameter (x-axis of regime map) ****
Set innerPar(parName) /
*   delta
*   alpha
   beta
*   phi
*   varepsilon
*   a_tech
*   taubar
/;

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
baseVal('delta')      = delta;
baseVal('alpha')      = alpha;
baseVal('beta')       = beta;
baseVal('phi')        = phi;
baseVal('varepsilon') = varepsilon;
baseVal('a_tech')     = a_tech;
baseVal('taubar')     = taubar;

* ============================================================
* Populate outer and inner grid values
* Applied independently to each axis.
* ============================================================

outerVal(outerSet) = 0;
if(outerPar('alpha') or outerPar('beta') or outerPar('phi') or outerPar('taubar'),
   outerVal(outerSet) = 0.1 + 0.1*(ord(outerSet) - 1);
);
if(outerPar('delta'),
   outerVal(outerSet) = 1.0000001 + 0.1*(ord(outerSet) - 1);
*   outerVal(outerSet) = 1.0000001 + 0.05*(ord(outerSet) - 1);
*    outerVal(outerSet) = 1.0000001 + 0.2*(ord(outerSet) - 1);
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
*   innerVal(innerSet) = 0.1 + 0.05*(ord(innerSet) - 1);
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
* Double loop
* ============================================================
loop(outerSet,

* --- Set outer parameter value ---
    delta      = baseVal('delta');
    alpha      = baseVal('alpha');
    beta       = baseVal('beta');
    phi        = baseVal('phi');
    varepsilon = baseVal('varepsilon');
    a_tech     = baseVal('a_tech');
    taubar     = baseVal('taubar');

    if(outerPar('delta'),      delta      = outerVal(outerSet));
    if(outerPar('alpha'),      alpha      = outerVal(outerSet));
    if(outerPar('beta'),       beta       = outerVal(outerSet));
    if(outerPar('phi'),        phi        = outerVal(outerSet));
    if(outerPar('varepsilon'), varepsilon = outerVal(outerSet));
    if(outerPar('a_tech'),     a_tech     = outerVal(outerSet));
    if(outerPar('taubar'),     taubar     = outerVal(outerSet));

* --- Inner loop ---
    loop(innerSet,

*   Reset to baseline before applying outer and inner parameters
        delta      = baseVal('delta');
        alpha      = baseVal('alpha');
        beta       = baseVal('beta');
        phi        = baseVal('phi');
        varepsilon = baseVal('varepsilon');
        a_tech     = baseVal('a_tech');
        taubar     = baseVal('taubar');

*   Re-apply outer parameter (so inner does not clobber it)
        if(outerPar('delta'),      delta      = outerVal(outerSet));
        if(outerPar('alpha'),      alpha      = outerVal(outerSet));
        if(outerPar('beta'),       beta       = outerVal(outerSet));
        if(outerPar('phi'),        phi        = outerVal(outerSet));
        if(outerPar('varepsilon'), varepsilon = outerVal(outerSet));
        if(outerPar('a_tech'),     a_tech     = outerVal(outerSet));
        if(outerPar('taubar'),     taubar     = outerVal(outerSet));

*   Apply inner parameter
        if(innerPar('delta'),      delta      = innerVal(innerSet));
        if(innerPar('alpha'),      alpha      = innerVal(innerSet));
        if(innerPar('beta'),       beta       = innerVal(innerSet));
        if(innerPar('phi'),        phi        = innerVal(innerSet));
        if(innerPar('varepsilon'), varepsilon = innerVal(innerSet));
        if(innerPar('a_tech'),     a_tech     = innerVal(innerSet));
        if(innerPar('taubar'),     taubar     = innerVal(innerSet));

*   Admissibility checks (skip inadmissible cells, store -999)
        if(alpha <= 0 or alpha >= 1
        or varepsilon <= 1
        or phi <= 0 or phi >= 1
        or taubar <= 0 or taubar > 1
        or beta <= 0 or beta >= 1
        or delta < 1,

            res_2d(outerSet,innerSet,'feasible') = 0;
            res_2d(outerSet,innerSet,'regime')   = -999;

        else

*       Recalibrate derived objects
            Zconst   = varepsilon**(-2*varepsilon) * (varepsilon-1)**(2*varepsilon-1);
            mMarkup  = varepsilon/(varepsilon - 1);
            piIUnder = Zconst * (a_tech**varepsilon);
            piUnder  = (1 + mMarkup) * piIUnder;
            DeltaInv = Zconst * (a_tech**varepsilon) * (phi**(1-varepsilon) - 1);
            DeltaF   = mMarkup * DeltaInv;
            DeltaTot = (1 + mMarkup) * DeltaInv;
            P0       = beta * DeltaInv;

*           Recompute Main Model B constants (depend on alpha, beta, DeltaInv)
            B_sigma   = (DeltaInv*beta)**(-0.5) * alpha**(-alpha/2)      * (1 - alpha)**((alpha - 1)/2);
            B_l       = (DeltaInv*beta)**( 0.5) * alpha**((2 - alpha)/2) * (1 - alpha)**((alpha - 1)/2);
            B_epsilon = (DeltaInv*beta)**( 0.5) * alpha**(-alpha/2)      * (1 - alpha)**((1 + alpha)/2);

            if(DeltaInv <= epsN,
                res_2d(outerSet,innerSet,'feasible') = 0;
                res_2d(outerSet,innerSet,'regime')   = -999;
            else

*           Starting values (conservative, keep Nvar and Dbig positive)
                tau.l     = min(0.20, taubar/2);
                c.l       = min(0.05, max(0, 1 - tau.l - 0.10));
                b.l       = min(0.05, tau.l);
                Nvar.l    = 1 - tau.l - c.l;
                DbigVar.l = 1 - tau.l + b.l;

                if(Nvar.l <= epsN,
                   c.l    = 0;
                   Nvar.l = 1 - tau.l;
                );
                if(DbigVar.l <= epsN,
                   b.l       = 0;
                   DbigVar.l = 1 - tau.l;
                );

                lam1.l = 0;   lam2.l = 0;   lam3.l = 0;

                solve mMainNewFull using mcp;

*           Post-solve reporting
                DbigVal  = DbigVar.l;
                NVal     = Nvar.l;
                plVal    = NVal/DbigVal;
                peVal    = 1/DbigVal;

*               Main Model input demands (Online Appendix, equations (34)-(35))
                lVal = DbigVal**0.5 * NVal**((alpha - 2)/2) * B_l;
                eVal = DbigVal**0.5 * NVal**(alpha/2)       * B_epsilon;

                gVal     = alpha*log(lVal) + (1-alpha)*log(eVal);
                sigmaVal = 1 - DbigVal**(-0.5) * NVal**(alpha/2) * B_sigma;

                WVal = piUnder + DeltaTot*sigmaVal - lVal - eVal
                     + (delta-1)*( tau.l*(piUnder + DeltaTot*sigmaVal - lVal)
                                 - b.l*P0*sigmaVal
                                 - c.l*lVal );

                dsig_dgVal = 1 - sigmaVal;
                dg_dplVal  = -alpha/(2*plVal);
                dg_dpeVal  = -(1-alpha)/(2*peVal);

                dl_dplVal  = -(2-alpha)*lVal/(2*plVal);
                dl_dpeVal  = (1-alpha)*lVal/(2*peVal);
                de_dplVal  = alpha*eVal/(2*plVal);
                de_dpeVal  = -(1+alpha)*eVal/(2*peVal);

                dpl_dtauVal = -(b.l + c.l)/sqr(DbigVal);
                dpe_dtauVal = 1/sqr(DbigVal);
                dpl_dbVal   = -(1 - tau.l - c.l)/sqr(DbigVal);
                dpe_dbVal   = -1/sqr(DbigVal);
                dpl_dcVal   = -1/DbigVal;
                dpe_dcVal   = 0;

                AlVal = (tau.l*DeltaTot - b.l*P0)*dsig_dgVal*dg_dplVal
                      - (tau.l + c.l)*dl_dplVal;
                AeVal = (tau.l*DeltaTot - b.l*P0)*dsig_dgVal*dg_dpeVal
                      - (tau.l + c.l)*dl_dpeVal;

                BlVal = DeltaTot*dsig_dgVal*dg_dplVal
                      - (dl_dplVal + de_dplVal);
                BeVal = DeltaTot*dsig_dgVal*dg_dpeVal
                      - (dl_dpeVal + de_dpeVal);

                dWdTauVal = (delta-1)*(piUnder + DeltaTot*sigmaVal - lVal)
                          + (delta-1)*(AlVal*dpl_dtauVal + AeVal*dpe_dtauVal)
                          + BlVal*dpl_dtauVal + BeVal*dpe_dtauVal;

                dWdCVal   = (delta-1)*(-lVal + AlVal*dpl_dcVal)
                          + BlVal*dpl_dcVal;

                dWdBVal   = (delta-1)*(-sigmaVal*P0 + AlVal*dpl_dbVal + AeVal*dpe_dbVal)
                          + BlVal*dpl_dbVal + BeVal*dpe_dbVal;

* -----------------------------------------------------------------
*   REGIME CLASSIFICATION (Online Appendix, Section 2.4 and Table 1)
*   Two top-level regimes:
*     1 = tau interior (lambda1 = 0), corresponding to Regimes 1.1-1.3:
*         1.1 = No instruments:  b ~ 0 and c ~ 0
*         1.2 = PB only:         0 < b < tau, c ~ 0
*         1.3 = PB exhausted:    b ~ tau
*     2 = tau constrained at taubar: lam1 > tol (Regimes 2.1-2.6)
*         2.1 = No instruments:  b ~ 0 and c ~ 0
*         2.2 = Credit only:     b ~ 0 and c > tol
*         2.3 = PB interior, credit inactive: 0 < b < tau, c ~ 0
*         2.4 = PB interior, credit active:   0 < b < tau, c > tol
*         2.5 = PB exhausted, credit inactive: b ~ tau, c ~ 0
*         2.6 = PB exhausted, credit active:   b ~ tau, c > tol
*
*   Tolerance: 1e-4
* -----------------------------------------------------------------
regimeVal = 0;
if(lam1.l > tolReg or abs(tau.l - taubar) < tolReg,
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
    if(b.l < tolReg and c.l < tolReg,
        regimeVal = 1.1;
    elseif abs(b.l - tau.l) < tolReg,
        regimeVal = 1.3;
    else
        regimeVal = 1.2;
    );
);

*           Store results
                res_2d(outerSet,innerSet,'feasible')   = 1;
                res_2d(outerSet,innerSet,'outerVal')   = outerVal(outerSet);
                res_2d(outerSet,innerSet,'innerVal')   = innerVal(innerSet);

                res_2d(outerSet,innerSet,'delta')      = delta;
                res_2d(outerSet,innerSet,'alpha')      = alpha;
                res_2d(outerSet,innerSet,'beta')       = beta;
                res_2d(outerSet,innerSet,'phi')        = phi;
                res_2d(outerSet,innerSet,'varepsilon') = varepsilon;
                res_2d(outerSet,innerSet,'a_tech')     = a_tech;
                res_2d(outerSet,innerSet,'taubar')     = taubar + 1e-12;

                res_2d(outerSet,innerSet,'piUnder')    = piUnder;
                res_2d(outerSet,innerSet,'DeltaInv')   = DeltaInv;
                res_2d(outerSet,innerSet,'DeltaF')     = DeltaF;
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
                res_2d(outerSet,innerSet,'r')          = gVal;
                res_2d(outerSet,innerSet,'sigma')      = sigmaVal + 1e-12;
                res_2d(outerSet,innerSet,'W')          = WVal;

                res_2d(outerSet,innerSet,'dWdTau')     = dWdTauVal;
                res_2d(outerSet,innerSet,'dWdC')       = dWdCVal;
                res_2d(outerSet,innerSet,'dWdB')       = dWdBVal;

                res_2d(outerSet,innerSet,'Al')         = AlVal;
                res_2d(outerSet,innerSet,'Ae')         = AeVal;
                res_2d(outerSet,innerSet,'Bl')         = BlVal;
                res_2d(outerSet,innerSet,'Be')         = BeVal;

                res_2d(outerSet,innerSet,'lam1')       = lam1.l + 1e-12;
                res_2d(outerSet,innerSet,'lam2')       = lam2.l + 1e-12;
                res_2d(outerSet,innerSet,'lam3')       = lam3.l + 1e-12;

                res_2d(outerSet,innerSet,'regime')     = regimeVal;
            );
        );
    );
);


* ============================================================
* Display and export
* ============================================================

display res_2d;

execute_unload "res_Main_v6.gdx", res_2d;
execute 'gdxxrw.exe res_Main_v6.gdx O=res_Main_v6.xlsx par=res_2d rng=RES!A2';
execute 'xlstalk.exe -O res_Main_v6.xlsx';

* ============================================================
* End of file
* ============================================================

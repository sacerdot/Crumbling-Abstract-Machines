(**************************************************************************)
(*       ___                                                              *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||         The HELM team.                                      *)
(*      ||A||         http://helm.cs.unibo.it                             *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU General Public License Version 2                  *)
(*                                                                        *)
(**************************************************************************)

include "alpha.ma".
include "pif_subst.ma".

let rec replace (t : pTerm) (s : pSubst) : pTerm ≝
  match t with
  [ val_to_term v ⇒ match v with
    [ pvar pv ⇒ match s with
      [ psubst nv pt ⇒ match veqb nv pv with
        [ true ⇒ pt
        | false ⇒ t ]
      ] 
    | abstr x t1 ⇒ match s with
      [ psubst nv pt ⇒ match veqb nv x with
        [ true ⇒ t
        | false ⇒ val_to_term ( abstr x ( replace t1 s ) ) ]
      ]
    ]
  | appl t1 t2 ⇒ appl ( replace t1 s ) ( replace t2 s ) ]
.

let rec evaluate (x : Variable) ve on ve : Bite ≝
  match ve with
  [ Epsilon ⇒ CValue (var x)
  | Snoc ve1 vs1 ⇒ match vs1 with
    [ subst v1 b1 ⇒ match veqb v1 x with
      [ true ⇒ b1
      | false ⇒ evaluate x ve1 ]
    ]
  ]
.

inductive PifTrans : pTerm → pTerm → Prop ≝ 
| beta_v : ∀v1, t1, t2. PifTrans (appl (val_to_term (abstr v1 t1)) t2) (p_subst t1 (psubst v1 t2)).

inductive TCTrans : Crumble → Crumble → Prop ≝
| cbeta_v : ∀x, b, e, v, ev. VEnvironment ev
 → TCTrans (CCrumble (AppValue (lambda x (CCrumble b e)) v) ev) (at (pi1 … (alpha b (push e [x ← CValue v]) ? ? ) ) ev)
| sub_var : ∀x, ev. VEnvironment ev
 → domb_e x ev = true
  → TCTrans (CCrumble (CValue (var x)) ev) (CCrumble (evaluate x ev) ev)
| sub_t : ∀x, v, v', ev. VEnvironment ev
 → domb_e x ev = true
  → evaluate x ev = CValue v'
   → TCTrans (CCrumble (AppValue (var x) v) ev) (CCrumble (AppValue v' v) ev)
. // qed.

inductive CTrans : Crumble → Crumble → Prop ≝
(*| no_step : ∀c. CTrans c c*)
| top_step : ∀c1, c2. TCTrans c1 c2
 → CTrans c1 c2
| closure_step : ∀c1, c2, cc1, cc2. CTrans c1 c2
 → CTrans (plug_c cc1 c1) (plug_c cc2 c2)
.

definition normal_c ≝ λc. ∀c'. ¬CTrans c c'.


inductive reachable_c : Crumble → Crumble → Prop ≝
| selfT : ∀c. reachable_c c c
| recurT : ∀c, c', c''. reachable_c c c' → CTrans c' c'' → reachable_c c c''
.


definition reachable_Crumble ≝ λc'. ∃t. ∃s. closed_t t
 → CTrans (match underline_pTerm t s with [ mk_Prod c n ⇒ c]) c'.


definition valZ : Variable ≝ variable 0.
definition termZ : pTerm ≝ val_to_term (pvar valZ).
definition valX : Variable ≝ variable 1.
definition termY : pTerm ≝ val_to_term (pvar (variable 2)).
definition abstr0 : pValue ≝ abstr valX termZ.
definition term0 : pTerm ≝ appl (val_to_term abstr0) termY.
definition abstr1 : pValue ≝ abstr valZ termZ.
definition term1 : pTerm ≝ appl (val_to_term abstr1) termY.

definition v0: Value ≝ var ν0.
definition b0: Bite ≝ CValue v0.
definition e0: Environment ≝ Epsilon.
definition e1: Environment ≝ Snoc e0 [ν0 ← b0].
definition v1: Value ≝ var ν1.
definition e2: Environment ≝ Snoc e0 [ν1 ← b0].
definition c0: Crumble ≝ 〈 b0, e1 〉.
definition abs0: Value ≝ lambda (ν0) c0 .
definition b1: Bite ≝ CValue abs0 .
definition c1: Crumble ≝ 〈 b1, e0 〉.
definition c2: Crumble ≝ 〈 (AppValue (lambda (ν1) c0) v0), e0 〉.
(*TODO test CTrans*)
lemma Veo : VEnvironment e0.
@PEpsilon qed.
(* (λv1.c0)v0,e0 ⇒ (c0@[v1←v0])^α@e0*)
(*lemma cTransTest0 : CTrans c2 ((at (pi1 … (alpha b0 (push e1 [(ν1) ← (CValue v0)]) ? ? )) e0)).
[ @cbeta_v @Veo qed.
(*c0 ⇒ c0*)
(*
lemma cTransTest1 : CTrans c0 c0.
@sub_var @PSnoc [@Veo | @Psubst @PValue @
*)
(* (λx.z) y ⇒βv z*)
lemma trans_test : PifTrans term0 termZ.
@beta_v qed.
(* (λz.z) y ⇒βv y*)
lemma trans_test2 : PifTrans term1 termY.
@beta_v qed.
*)
lemma p_e_to_s : ∀e, s. VEnvironment (Snoc e s) → PracticalSubstitution s.
#e #s #H(* lapply (refl … (Snoc e s)) cases H in ⊢(? ? ? %→ ?);*)
inversion H
[ #abs destruct
| #e' #s' #He' #Hs' #_ #eq destruct //
] qed.

lemma p_e_to_e : ∀e, s. VEnvironment (Snoc e s) → VEnvironment e.
#e #s #H inversion H
[ #abs destruct
| #e0 #s0 #He0 #Hs0 #_ #eq destruct //
] qed.

lemma pract_env_concat : ∀e1, e2. VEnvironment e1 → VEnvironment e2 → VEnvironment (concat e1 e2).
#e1 #e2 #H1 #H2 cases H2
[ normalize @H1
| @Environment_simple_ind2
 [ #s2' #H0 #Hs2' normalize @PSnoc [ // | // ]
 | #e3 #s3 normalize #H3 #s4 #H5 #H6 @PSnoc
  [ @H3
   [ @(p_e_to_e e3 s3) // | @(p_e_to_s e3 s3) // ]
  | // ]
 ]
] qed.

lemma p_vc_to_e : ∀b, e. V_Crumble〈b, e〉→ VEnvironment e.
#b #e #H inversion H
#b0 #e0 #_ #Venv #eq destruct @Venv
qed.

lemma p_ve_to_e : ∀b, e. VE_Crumble〈b, e〉→ VEnvironment e.
#b #e #H0 inversion H0
#b' #e' #H1 #eq destruct //
qed.

lemma p_vc_to_b : ∀b, e. V_Crumble 〈b, e〉 → PracticalBite b.
#b #e #H inversion H
#b0 #e0 #H2 #_ #eq destruct //
qed.

lemma p_b_to_eb : ∀b, v. b = CValue v
→ PracticalBite b
 → EPracticalBite b.
#b #v #eq #H inversion H
[ #v0 #CPVal #eq2 @EPValue @CPVal
| #v1 #v2 #_ #_ #eq2 destruct
qed.

lemma p_s_to_eb : ∀v, b. PracticalSubstitution (subst v b) → EPracticalBite b.
#v #b #H1 inversion H1
#v' #b' #H2 #eq destruct //
qed.

lemma p_eb_to_v : ∀v. EPracticalBite (CValue v) → CPracticalValue v.
#v #H1 inversion H1 #v' #H2 #eq destruct //
qed.

lemma p_b_to_v : ∀v. PracticalBite (CValue v) → CPracticalValue v.
#v #H1 inversion H1
[ #v' #H2 #eq destruct //
| #v1 #v2 #H2 #H3 #eq destruct ]
qed.

lemma p_ab_to_v1 : ∀v1, v2. PracticalBite (AppValue v1 v2) → CPracticalValue v1.
#v1 #v2 #H1 inversion H1
[ #v #H2 #eq destruct
| #v1' #v2' #H2 #H3 #eq destruct //
] qed.

lemma p_ab_to_v2 : ∀v1, v2. PracticalBite (AppValue v1 v2) → CPracticalValue v2.
#v1 #v2 #H1 inversion H1
[ #v #H2 #eq destruct
| #v1' #v2' #H2 #H3 #eq destruct //
] qed.

lemma pract_ren : ∀b1, e, v, b2, v'.
 VE_Crumble 〈b1, (Snoc e (subst v b2))〉
  → (veqb (ν (fresh_var〈b1, (Snoc e (subst v b2))〉)) v' = true)
   → VE_Crumble 〈b1, (Snoc e (subst v' b2))〉.
#b1 (@Environment_simple_ind2)
[ #v #b2 #v' #H1 #eq @PCCrumble @PSnoc // @Psubst @(p_s_to_eb v b2) @(p_e_to_s Epsilon [v←b2]) @(p_ve_to_e b1 (Snoc Epsilon [v←b2])) //
| #e #s #H1 #v #b2 #v' #H2 #veq @PCCrumble @PSnoc
 [ @PSnoc
  [ @(p_e_to_e e s) @(p_e_to_e (Snoc e s) [v←b2]) @(p_ve_to_e b1 (Snoc (Snoc e s) [v←b2])) //
  | @(p_e_to_s e s) @(p_e_to_e (Snoc e s) [v←b2]) @(p_ve_to_e b1 (Snoc (Snoc e s) [v←b2])) // ]
 | @Psubst @(p_s_to_eb v b2) @(p_e_to_s (Snoc e s) [v←b2]) @(p_ve_to_e b1 (Snoc (Snoc e s) [v←b2])) // ]
] qed.

lemma pract_ssv : ∀v, y, z. ∀(H: inb_v z v = false). CPracticalValue v → CPracticalValue (ssv v y z H).
*
[ #v #y #z #H #H1 lapply (refl … (var v)) cases H1 in ⊢(? ? ? %→ ?); #v' #c #eq destruct
| #v' #c #y #z #H #H1 whd in ⊢(? %); cases (veqb v' y)
 [ normalize //
 | normalize @Plambda ]
] qed.

lemma pract_ssb : ∀b, y, z. ∀(H: inb_b z b = false). PracticalBite b → PracticalBite (ssb b y z H).
*
[ #val #y #z #H #H1 whd in ⊢ (? %); @PValue @pract_ssv @p_b_to_v //
| #v1 #v2 #y #z #H #H1 whd in ⊢(? %); @PAppValue
 [ @p_b_to_v @PValue @pract_ssv @(p_ab_to_v1 v1 v2) //
 | @p_b_to_v @PValue @pract_ssv @(p_ab_to_v2 v1 v2) //
] qed.

lemma pract_sseb : ∀b, y, z. ∀(H: inb_b z b = false). EPracticalBite b → EPracticalBite (ssb b y z H).
*
[ #v #y #z #H #EP whd in ⊢ (? %); @EPValue @pract_ssv @p_eb_to_v @EP
| #v1 #v2 #y #z #H #EP whd in ⊢ (? %); inversion EP #H5 #H6 #H7 destruct ]
qed.

lemma pract_sse : ∀e, y, z. ∀(H: inb_e z e = false). VEnvironment e → VEnvironment (sse e y z H).
@Environment_simple_ind2
[ //
| #e * #v #b #H1 #y #z #H0 #H2 whd in match (sse ? ? ? ?); inversion (veqb y v)
 [ #eq whd in ⊢ (? %); @PSnoc
  [ @H1 @p_e_to_e //
  | @Psubst @pract_sseb @(p_s_to_eb v) @(p_e_to_s e) // ]
 | #eq whd in ⊢ (? %); @PSnoc
  [ @H1 @(p_e_to_e e [v←b]) //
  | @Psubst @pract_sseb @(p_s_to_eb v) @(p_e_to_s e) // ] ]
] qed. 

lemma pract_at : ∀b1, e1, e2. VE_Crumble〈b1, e1〉→ VEnvironment e2 → VE_Crumble (at〈b1, e1〉 e2).
#b1 #e1 #e2 #H0 #H1 normalize @PCCrumble @(pract_env_concat e1 e2)
[ @(p_ve_to_e b1 e1) // | // ]
qed.

lemma pract_alpha : ∀b, e. ∀n. ∀(H: fresh_var 〈b, e〉≤ n). VE_Crumble〈b, e〉 → VE_Crumble (pi1 Crumble ? (alpha b e n H)).
#b (@Environment_simple_ind2)
[ //
| #e * #v' #b' #H1 #n #H2 #H3 whd in match (fresh_var ?); whd in match (alpha ? ? ? ?);
 lapply (H1 (S n)) cases (alpha b e (S n)) * #b'' #e' #KK #H4
 whd in match ( match «〈b'',e'〉,?»
      in Sig
      with 
     [mk_Sig a h⇒
      «at (ssc a ? (νn) ?) (Snoc Epsilon [νn←b']),
      ?»]);
 @pract_at
 [ @PCCrumble @pract_sse @(p_ve_to_e b'') @H4
  [ @(alpha_aux1 b e ([v'←b']) n) //
  | @PCCrumble @(p_e_to_e e [v'←b']) @(p_ve_to_e b) // ]
 | @PSnoc [ // | @Psubst @(p_s_to_eb v') @(p_e_to_s e) @(p_ve_to_e b) // ]
] qed.
(*
lemma pract_cbeta_v : ∀x, b, e, v, ev, n. ∀(H: fresh_var 〈b,(push e [x←CValue v])〉≤n).
CTrans 〈 AppValue (lambda x 〈 b, e〉) v, ev〉 (at (pi1 …(alpha b (push e [x←CValue v]) n H)) ev)
 → VE_Crumble (at (pi1 …(alpha b (push e [x←CValue v]) n H)) ev).
#x #b #e #v #ev #n #H #H0 whd in match (alpha ? ? ? ?); 
@(pract_alpha b (push e [x←CValue v]) n H)

lemma pract_sub_var : ∀x, ev. CTrans 〈CValue (var x), ev〉〈evaluate x ev, ev〉
 → VE_Crumble 〈evaluate x ev, ev〉.

lemma pract_sub_t :

lemma pract_trans : ∀b1, e1, b2, e2. (VE_Crumble 〈b1, e1〉) → (CTrans 〈b1, e1〉 〈b2, e2〉) → VE_Crumble 〈b2, e2〉.
#b1 #e1 #b2 @Environment_simple_ind2
[ #H1 #H2 @PCCrumble //
| #e2 #s2 #H1 #H2 #H3 cases H3
*)

let rec is_value_b (b: Bite) ≝
  match b with
  [ CValue v ⇒ True
  | AppValue v1 v2 ⇒ False
  ]
.

let rec is_lambda_b (b: Bite) ≝
  match b with
  [ CValue v ⇒ match v with
    [ var x ⇒ false
    | lambda z c ⇒ true ]
  | AppValue v1 v2 ⇒ false
  ]
.

let rec is_value_t (t: pTerm) ≝
  match t with
  [ val_to_term v ⇒ True
  | appl t1 t2 ⇒ False
  ]
.

lemma NPract_x: ∀c, b, e, x. c = 〈b, e〉
→ b = CValue (var x)
 → closed_c c
  → domb_e x e = false
   → False.
#c #b #e #x #eq0 #eq1 #clos #dom
lapply clos normalize #clos1 lapply (clos1 x) destruct normalize cut (veqb x x = true)
 [@eq_to_veq // | #veq >veq normalize >dom normalize #abs @(absurd (true=false)) //
qed.

lemma NPract_App_x: ∀c, b, e, x, v. c = 〈b, e〉
→ b = AppValue (var x) v
 → closed_c c
  → domb_e x e = false
   → False.
#c #b #e #x #v #eq1 #eq2 #clos #dom
lapply clos normalize #clos1 lapply (clos1 x) destruct normalize cut (veqb x x = true)
 [@eq_to_veq // | #veq >veq normalize >dom normalize #abs @(absurd (true=false)) //
qed.


     
(*
lemma closed_to_lam: ∀c, b, e. normal_c c
→ closed_c c
 → c= 〈b, e〉
  → is_lambda_b b = true.
#c *
[ *
 [ #v #e #norm #clos #eq normalize | #H1 #H2 #H3 #H4 #H5 #H6 normalize // ] |(*ottieni assurdo CTrans e ¬CTrans o esegui*)
  lapply norm normalize #norm1 inversion b
*)
lemma D_one: ∀v, v', x. is_value_t v
→ is_value_t v'
 → is_value_t (replace v (psubst x v')).
*
[ #v *
 [ #v' #x #H1 #H2 cases v
  [ #v1 normalize cases (veqb x v1)
   [ whd in ⊢(? %); //
   | whd in ⊢(? %); // ]
  | #y #t1' normalize cases (veqb x y)
   [ whd in ⊢(? %); //
   | whd in ⊢(? %); // ]
  ]
 | #t1 #t2 #x #H1 #H2 elim H2 ]
| #t1 #t2 #v' #x #H1 elim H1 ]
qed.

lemma witness: ∀x, e. domb_e x e = true
→ VEnvironment e
 → ∃v. evaluate x e = CValue v.
#x @Environment_simple_ind2
[ whd in match (domb_e ? ?); #abs #Venv % //
| #e * #v' *
 [ #v #H1 #dom #Venv whd in match (evaluate ? ?); inversion (veqb v' x)
  [ #eq normalize % //
  | #eq normalize @H1
   [ lapply dom whd in match (domb_e ? ?); lapply (veqb_comm v' x) #eq2 <eq2 >eq normalize //
   | @(p_e_to_e e [v' ← CValue v]) @Venv ]
  ]
 | #v1 #v2 #H1 #dom #Venv cut (PracticalSubstitution [v'←AppValue v1 v2])
  [ @(p_e_to_s e ?) @Venv | #Psubst cut (EPracticalBite (AppValue v1 v2))
   [ @(p_s_to_eb v' ?) @Psubst | #EP inversion EP #v #CPr #eq destruct ]
  ]
 ]
] qed.
(*
lemma aux_rb_to_abst: ∀ev, x. VEnvironment ev
→ domb_e x ev = true
 → ∃y, t. aux_read_back (val_to_term (pvar x)) ev = val_to_term (abstr y t).
@Environment_simple_ind2
[ #x #Venv whd in match (domb_e ? ?); #abs destruct
| #e * #z #b #H1 #x #Venv #dom whd in match (aux_read_back ? ?); whd in match (match psubst z (read_back_b b) in pSubst return λ_:pSubst.Variable with 
     [psubst (y0:Variable)   (t':pTerm)⇒y0]); whd in match (match psubst z (read_back_b b) in pSubst return λ_:pSubst.pTerm with 
     [psubst (y0:Variable)   (t':pTerm)⇒t']); inversion (veqb x z)
 [ cut (domb_e x e = false) lapply (H1 x ? ?)
  [ lapply dom whd in match (domb_e ? ?); >veq normalize


lemma read_back_to_abst: ∀ev, x. VEnvironment ev
→ domb_e x ev = true
 → ∃e1, e2. ev = concat e1 e2
  → ∃y, c. read_back 〈CValue (var x), ev〉 = read_back 〈CValue (lambda y c), e2〉.
@Environment_simple_ind2
[ #x #Venv whd in match (domb_e ? ?); #abs destruct
| #e #s #H1 #x #Venv #dom whd in match (read_back ?); whd in match (read_back_b ?);
 inversion (inb_s x s) #inb lapply (H1 x ? ?) whd in match (aux_read_back ? ?);   
*)


(*
lemma D_two: ∀ev, v'. VEnvironment ev
(*→ b = CValue v'*)
 →  ∃pv'. read_back 〈CValue v', ev〉= val_to_term pv'.
@Environment_simple_ind2
[ *
 [ #x #Venv normalize % //
 | #x * #b' #e'#Venv whd in match (read_back ?); % // ]
| #e1 #s1 #H1 *
 [ #x #Venv inversion (domb_e x (Snoc e1 s1))
  [ #domT lapply (witness x
  
lemma read_back_to_abs: ∀ev, x. VEnvironment ev
→ domb_e x ev = true
 → ∃e1, e2. ev = concat e1 e2
  → ∃y, c. read_back 〈CValue (var x), ev〉 = read_back 〈CValue (abstr y c), e2〉.


 whd in match (aux_read_back ? ?); % //
 | @Environment_simple_ind2
  [ * #x' #b1 whd in match (aux_read_back ? ?); cases ev
  [ whd in match (aux_read_back ? ?); whd in match (match psubst x' (read_back_b b1) in pSubst return λ_:pSubst.Variable with 
    [psubst (y:Variable)   (t':pTerm)⇒y]); whd in match (match psubst x' (read_back_b b1) in pSubst return λ_:pSubst.pTerm with 
    [psubst (y:Variable)   (t':pTerm)⇒t']); whd in match (p_subst_sig ? x' ? ? ?); cases (veqb x' var')
*)

lemma D_three: ∀c, b, ev, x, v, y, c'. c = 〈b, ev〉
→ VEnvironment ev
 → b = CValue (lambda y c') ∨ b = CValue (var x) ∨ (b = AppValue (var x) v)
  → closed_c c
   → well_named c = true
    → domb_e x ev = false
     → V_Crumble c.
#c #b #ev #x #v #y #c' #eq #Venv #or #closeC #WNc #nDomx
cases or
[ #or1 cases or1
 [ #H1 destruct @PCrumble
  [ @PValue @Plambda | // ]
 | #H2 lapply (NPract_x c b ev x eq H2 closeC nDomx) #abs elim abs
 ]
| #H3 lapply (NPract_App_x c b ev x v eq H3 closeC nDomx) #abs elim abs
] qed.

lemma normal_value: ∀c, b, v, e. b = CValue v
→c = 〈b, e〉
 → VEnvironment e
  → closed_c c
   → well_named c = true
    → normal_c c
     → V_Crumble c.
#c #b *
[ #x #e #eq1 #eq2 #VEnv #clos #wnamed #norm inversion (domb_e x e)
 [ #domb cut (TCTrans c (CCrumble (evaluate x e) e))
  [ destruct @(sub_var x e VEnv domb)
  | #Trans lapply norm normalize #norm1 lapply (norm1 〈evaluate x e,e〉) #abs elim abs #abs1 lapply (top_step ? ? Trans) #Trans2 lapply (abs1 Trans2) #False elim False ]
 | #ndom @(D_three c ? e x ? ? ? eq2 VEnv ? clos wnamed ndom) [ // | // | // | @or_introl @or_intror // ] ]
| #y #c' #e #eq1 #eq2 #VEnv #clos #wnamed #norm destruct @PCrumble
 [ @PValue @Plambda | @VEnv ]
] qed.



lemma D_four: ∀c, b, e. c = 〈b, e〉
→ VEnvironment e
 → closed_c c
  → well_named c = true
   → normal_c c
    → V_Crumble c.
#c *
[ #v #e #eq #VEnv #clos #wnamed #norm @(normal_value c (CValue v) v e ? eq VEnv clos wnamed norm) //
| *
 [ #x #v1 #e #eq #VEnv #clos #wnamed #norm inversion (domb_e x e)
  [ #domt lapply (witness x e domt VEnv) #evCV lapply evCV * #v' #evCV' cut (CTrans c (CCrumble (AppValue v' v1) e))
   [ destruct @top_step @(sub_t x v1 v' e VEnv domt evCV')
   | #abs0 lapply norm normalize #nCTr lapply (nCTr  〈AppValue v' v1,e〉) #abs1 elim abs1 #abs2 lapply (abs2 abs0) #False elim False
   ]
  | #domf @(D_three ? (AppValue (var x) v1) e x v1 ? ? eq VEnv ? clos wnamed domf) // ]
 | #x * #b #e #v #ev #eq #Venv #clos #wnamed #norm cases (absurd ? ? (norm …)) [ destruct @top_step % @Venv | skip ]
] qed.

lemma concat_to_push :∀e, s. concat (Snoc Epsilon s) e = push e s.
@Environment_simple_ind2
[ #s normalize //
| #e #s #HI #t normalize >HI //
] qed.
(* qui devo definire env_ind a partire dalla coda*)

lemma clos_step: ∀b, x, b', e. closed_c 〈b,concat (Snoc Epsilon [x←b']) e〉 → closed_c 〈b', e〉.
#b #x #b' #e whd in match (closed_c ?);
#clos whd in match (closed_c ?); #x0 lapply (clos x0)
whd in match (fvb ? ?); inversion (fvb_b x0 b∧¬domb_e x0 (concat (Snoc Epsilon [x←b']) e))
[ #eq whd in match (if true then true else fvb_e x0 (concat (Snoc Epsilon [x←b']) e) );
 #abs destruct
| lapply (domb_concat_distr x0 e (Snoc Epsilon [x←b'])) #eq3 >eq3
  whd in match (domb_e x0 (Snoc Epsilon [x←b']));
  #eq whd in match (if false then true else fvb_e x0 (concat (Snoc Epsilon [x←b']) e) );
  whd in match (fvb_e ? ?); lapply (fv_concat e (Snoc Epsilon [x←b']) x0) #eq1 >eq1
  whd in match (fvb_e x0 (Snoc ? ?)); #eq2 inversion (veqb x0 x)
  [ #veq lapply eq >veq whd in match (if true then true else domb_e x0 Epsilon ∨domb_e x0 e);
    #H whd in match (fvb ? ?); inversion (fvb_b x0 b'∧¬domb_e x0 e)
   [ #eq4 cases (? : False) lapply eq2 >eq4 normalize #abs destruct
   | #eq4 whd in match (if false then true else fvb_e x0 e); lapply eq2
     >eq4 normalize //
   ]
  | #veq lapply eq >veq whd in match (if false then true else domb_e x0 Epsilon ∨domb_e x0 e);
    #eq5 whd in match (fvb ? ?); inversion (fvb_b x0 b'∧¬domb_e x0 e)
   [ #eq6 cases (? : False) lapply eq2 >eq6 normalize #abs destruct
   | #eq6 whd in match (if false then true else fvb_e x0 e); lapply eq2 >eq6 normalize //
   ]
] qed.

lemma wnamed_step: ∀b, x, b', e. well_named 〈b,concat (Snoc Epsilon [x←b']) e〉 = true → well_named 〈b', e〉 = true.
#b #x #b' #e whd in match (well_named ?); inversion (well_named_b b∧well_named_e (concat (Snoc Epsilon [x←b']) e))
[ #H1 whd in match (if true then dist_dom (concat (Snoc Epsilon [x←b']) e) else false);
  lapply (dist_dom_concat (Snoc Epsilon [x←b']) e) #eq1 #H2 lapply (eq1 H2) #H3
  lapply (proj1 … H3) #H4 whd in match (well_named ?);
  lapply (well_named_concat e (Snoc Epsilon [x←b'])) #eq2 lapply H1 >eq2
  #H5 inversion (well_named_b b'∧well_named_e e)
 [ #eq3 whd in match (if true then dist_dom e else false); @(proj2 … H3)
 | #eq3 cases (? : False) lapply H5 whd in match (well_named_e (Snoc Epsilon [x←b'])); >eq3 normalize 
   cases (well_named_b b) [ normalize #abs destruct | normalize #abs destruct ]
 ]
| lapply (well_named_concat e (Snoc Epsilon [x←b'])) #eq >eq #H1
  whd in match (if false then dist_dom (concat (Snoc Epsilon [x←b']) e) else false);
  #abs destruct
] qed.

lemma five_dot_three : ∀e, b. closed_c 〈b, e〉
→ well_named 〈b, e〉 = true
 → ( normal_c 〈b, e〉 ↔ V_Crumble 〈b, e〉).
@Environment_reverse_ind
[ 2: #e' * #x #b' #IH #b #clos #wnamed %
 [ #norm  @(D_four ? b (concat (Snoc Epsilon  [x←b']) e') ? ? clos wnamed norm) //
  lapply (IH b' ? ?)
   [ @(wnamed_step b x b' e' wnamed)
   | @(clos_step b x b' e' clos)
   | cut (normal_c 〈b', e'〉)
    [ lapply norm whd in match (normal_c ?); #norm1 whd in match (normal_c ?);
      #c' lapply (norm1 c') @inverse #CTr cut (plug_c (crc b (envc Epsilon x)) 〈b', e'〉=〈b,concat (Snoc Epsilon [x←b']) e'〉)
     [ normalize //
     | #eq1 cut (plug_c (hole) c' = c') [ //
      | #eq2 <eq1 <eq2 @closure_step @CTr
      ]
     ]
    | #norm1 * #norm_to_vc #_ lapply (norm_to_vc norm1) #V_C @pract_env_concat
     [ @PSnoc [ @PEpsilon | @Psubst 
 |
 ]
| 1: #b #clos #wnamed %
 [ #norm @(D_four ? b Epsilon ? ? clos wnamed norm) //
 | #VC



#e @(Environment_reverse_ind ? ? ? e)
[ #b #clos #wnamed #norm @(D_four ? b Epsilon ? ? clos wnamed norm) [ // | @PEpsilon ]
| #e' * #x #b'  #IH #b #clos #wnamed #norm cut (normal_c 〈b', e'〉)
 [ whd in match (normal_c ?); #c' lapply norm whd in match (normal_c ?); #norm1 lapply (norm1 c')
  #norm2 @(not_to_not ? (CTrans (plug_c (crc b (envc e' x)) 〈b', Epsilon〉) (plug_c hole c')))
  [ 2: cut (plug_c (crc b (envc e' x)) 〈b', Epsilon〉 = 〈b,concat e' (Snoc Epsilon [x←b'])〉 ∧ plug_c hole c'=c')
   [ % [ normalize // | // ]
   | #andeq lapply (proj1 … andeq) #eq1 lapply (proj2 … andeq) #eq2 >eq1 >eq2 @norm2 ]
  | #CTr cases (? : False) inversion CTr
   [ #c1 #c2 #TCTr #eq1 #eq2 cut (CTrans 〈b,concat e' (Snoc Epsilon [x←b'])〉 c')
    [ cut (plug_c (crc b (envc e' x)) 〈b', Epsilon〉 = 〈b,concat e' (Snoc Epsilon [x←b'])〉 ∧ plug_c hole c'=c')
     [ % [ normalize // | // ]
     | #andeq lapply (proj1 … andeq) #eq3 lapply (proj2 … andeq) #eq4 <eq3 <eq4 @closure_step
   |
   ]
  ]
 |
    @(closure_step (CCrumble b' e') c' (crc b (envc e' x)) hole ?) inversion CTr
    [ #c1 #c2 #TCTr #eq1 #eq2 @TCTr | (* #c1 #c2 #cc1 #cc2 #TCTr #eq1 #eq2*)
      cut (plug_c (crc b (envc e' x)) 〈b', Epsilon〉 = 〈b,concat e' (Snoc Epsilon [x←b'])〉 ∧ plug_c hole c'=c')
     [ % [ normalize // | // ]
     | #andeq lapply (proj1 … andeq) #eq3 lapply (proj2 … andeq) #eq4
     lapply norm2 <eq3 <eq4 
    
     lapply CTr >eq1 >eq2
  cases (absurd ? ? (norm …)) whd in match (normal_c ?); #c' lapply norm whd in match (normal_c ?); #norm1
   cases (absurd ? ? (norm …)) 
   
(CTrans (plug_c (crc b (envc e' x)) 〈b', Epsilon〉) )


cut (V_Crumble 〈b', e'〉 ∧ normal_c 〈b', e'〉)
 [ 2: #H lapply (proj1 … H) #V_C lapply (proj2 … H) #norm2 @(D_four ? b (Snoc e' [x←b']) ? ? clos wnamed norm)
  [ // | @PSnoc
   [ @(p_vc_to_e b' e' V_C) | @Psubst lapply (p_vc_to_b b' e' V_C) #Pract inversion Pract
    [ #v #H1 #eq <eq @(p_b_to_eb b' v eq Pract)
    | #v1 #v2 #H1 #H2 #eq cases (? : False) inversion H1 #y * #b'' #e'' #eq2
      cases (absurd ? ? (norm2 …)) [ destruct @top_step @cbeta_v @(p_vc_to_e ? e' V_C) | skip ]
    ]
   ]
  ]
  | % 
   [ @(IH b' ? ? ?)
    [ whd in match (closed_c ?); #x0 lapply clos whd in match (closed_c ?); #clos0
     whd in match (fvb ? ?); inversion (fvb_b x0 b'∧¬domb_e x0 e')
     [ #eq0 lapply (clos0 x0) whd in match (fvb ? ?); inversion (fvb_b x0 b∧¬domb_e x0 (Snoc e' [x←b']))
      [ #eq2 whd in match (if true then true else fvb_e x0 (Snoc e' [x←b'])); #abs destruct
      | #eq2 whd in match (if false then true else fvb_e x0 (Snoc e' [x←b'])); inversion (fvb_e x0 e'∧¬veqb x0 x)
       [ #eq3 whd in match (if true then true else fvb_b x0 b'); #abs @abs
       | #eq3 whd in match (if false then true else fvb_b x0 b'); #fvbf lapply eq0 >fvbf
         whd in match (false∧¬domb_e x0 e'); #abs destruct ]
      ]
     | #eq0 whd in match (if false then true else fvb_e x0 e'); lapply (clos0 x0) whd in match (fvb ? ?);
       inversion (fvb_b x0 b∧¬domb_e x0 (Snoc e' [x←b']))
      [ #eq1 whd in match (if true then true else fvb_e x0 (Snoc e' [x←b'])); #abs destruct
      | #eq1 whd in match (if false then true else fvb_e x0 (Snoc e' [x←b'])); inversion (fvb_e x0 e'∧¬veqb x0 x)
       [ #eq2 whd in match (if true then true else fvb_b x0 b'); #abs destruct
       | #eq2 whd in match (if false then true else fvb_b x0 b'); #fvf inversion (veqb x0 x)
        [ #veq 
         
       ]
      ] 
     ]

     [ #H1 whd in match (if true then true else fvb_e x0 (Snoc e' [x←b'])); #abs destruct
     | #H1 whd in match (if false then true else fvb_e x0 (Snoc e' [x←b']));
       inversion (fvb_e x0 e'∧¬veqb x0 x)
      [ #H2 whd in match (if true then true else fvb_b x0 b'); #abs destruct
      | #H2 whd in match (if false then true else fvb_b x0 b'); #fvbx0b' whd in match (fvb ? ?);
        >fvbx0b' whd in match (false∧¬domb_e x0 e'); whd in match (if false then true else fvb_e x0 e');
        whd in match (fvb_e ? ?); cases H2
  
  
   check check 
  whd in match (closed_c ?); #x0 lapply clos whd in match (closed_c ?); #clos0 lapply (clos0 x0) #clos1 whd in match (fvb ? ?);
   inversion (fvb_b x0 b'∧¬domb_e x0 e')
    [ #eq lapply clos1 whd in match (fvb ? ?); cases (fvb_b x0 b∧¬domb_e x0 (Snoc e' [x←b']))
     [ normalize // | whd in match (if false then true else fvb_e x0 (Snoc e' [x←b']));
      whd in match (if true then true else fvb_e x0 e'); cases (fvb_b x0 b)
     [ normalize
    
     #clos0 lapply clos0 whd in match (fvb ? ?); normalize

 @(D_four ? b (Snoc e' [x←b']) ? ? clos wnamed norm)
 [ // |  
cut (normal_c 〈b', e'〉)
 [ 2: #norm' lapply (IH b' ? ? norm')
  [ cut (dist_dom e' = true)   whd in match (well_named ?); lapply wnamed  whd in match (well_named ?); cases (well_named_b b∧well_named_e (Snoc e' [x←b'])) [ 2: normalize #abs destruct
   | normalize change in match (if ? then ? else ?); with dist_dom (Snoc e' [x←b']); cut (well_named_e (Snoc e' [x←b'])= true) #wnamed' normalize 
*)

lemma five_dot_three_r : ∀c. closed_c c
→ well_named c
 → V_Crumble c
  → normal_c c.


lemma D_eight : ∀(t: pTerm). ∀(u: pTerm). ∀(x: Variable). ∀(v : pValue). (*per casi su veqb e fvb_t *)
 PifTrans t u
  → PifTrans (p_subst t (psubst x (val_to_term v))) (p_subst u (psubst x (val_to_term v))).
#t #u #x #v #H1 inversion H1 #v1 #t1 #t2 #eq1 #eq2  lapply (p_subst_distro (val_to_term (abstr v1 t1)) t2 (psubst x (val_to_term v))) #eq3 >eq3
lapply (no_subst2 v1 t1 (val_to_term v))









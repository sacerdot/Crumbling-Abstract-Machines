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

inductive PTTrans : pTerm → pTerm → Prop ≝ 
| beta_v : ∀v1, t1, t2. PTTrans (appl (val_to_term (abstr v1 t1)) t2) (p_subst t1 (psubst v1 t2)).

inductive PCTrans : pTerm → pTerm → Prop ≝
| pclos_step : ∀t, u, R. PTTrans t u
 → rv_context R
  → PCTrans (plug_t R t) (plug_t R u).

inductive PTrans : pTerm → pTerm → Prop ≝
| top_trans : ∀t, u. PTTrans t u → PTrans t u
| clos_trans : ∀t, u. PCTrans t u → PTrans t u
.
(*
** Devo evitare che la CTr che attiva la closure_step sia a sua volta una closure_step
** Quindi escludo alt 3
** Devo dimostrare:
**  - Lo step di normalità (normal 〈b,[x←b']e'〉 → normal 〈b', e'〉)
**  - ⇐ di 5.3
** Problema: per inversione mi trovo CTrans tra le ipotesi ma mi servirebbe TCTrans
** per dimostare l'assurdo 
**  - (CTrans c1 c2 ?→ TCTrans c1 c2)
**  - Devo porre delle condizioni su cc?
*)

(*
** Alternativa 1, TCT e CC → CT
*)

inductive TCTrans : Crumble → Crumble → Prop ≝
| cbeta_v : ∀x, b, e, v, ev. VEnvironment ev
 → TCTrans (〈(AppValue (lambda x (〈b, e〉)) v), ev〉) (at (pi1 … (alpha b (push e [x ← CValue v]) (fresh_var 〈b,push e [x←CValue v]〉) ? ) ) ev)
| sub_var : ∀x, ev. VEnvironment ev
 → domb_e x ev = true
  → TCTrans (CCrumble (CValue (var x)) ev) (CCrumble (evaluate x ev) ev)
| sub_t : ∀x, v, v', ev. VEnvironment ev
 → domb_e x ev = true
  → evaluate x ev = CValue v'
   → TCTrans (CCrumble (AppValue (var x) v) ev) (CCrumble (AppValue v' v) ev)
. // qed.

inductive CCTrans : Crumble → Crumble → Prop ≝
| closure_step : ∀c1, c2, cc. TCTrans c1 c2
 → CCTrans (plug_c cc c1) (plug_c cc c2)
.

inductive CTrans : Crumble → Crumble → Prop ≝
| top_step : ∀c1, c2. TCTrans c1 c2
 → CTrans c1 c2
| clos_step : ∀c1, c2. CCTrans c1 c2
 → CTrans c1 c2
.


(*
** Alternativa 2, TCT → CT, TCT → C〈CT〉
*)
(*
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
| top_step : ∀c1, c2. TCTrans c1 c2
 → CTrans c1 c2
| clos_step : ∀c1, c2, cc. TCTrans c1 c2
 → CTrans (plug_c cc c1) (plug_c cc c2)
.
*)

(*
** Alternativa 3, CT → CT
*)
(*
inductive CTrans : Crumble → Crumble → Prop ≝
| cbeta_v : ∀x, b, e, v, ev. VEnvironment ev
 → CTrans (CCrumble (AppValue (lambda x (CCrumble b e)) v) ev) (at (pi1 … (alpha b (push e [x ← CValue v]) ? ? ) ) ev)
| sub_var : ∀x, ev. VEnvironment ev
 → domb_e x ev = true
  → CTrans (CCrumble (CValue (var x)) ev) (CCrumble (evaluate x ev) ev)
| sub_t : ∀x, v, v', ev. VEnvironment ev
 → domb_e x ev = true
  → evaluate x ev = CValue v'
   → CTrans (CCrumble (AppValue (var x) v) ev) (CCrumble (AppValue v' v) ev)
| closure_step : ∀c1, c2, cc. CTrans c1 c2
 → CTrans (plug_c cc c1) (plug_c cc c2)
. // qed.
*)

definition normal_c ≝ λc. ∀c'. ¬(CTrans c c').

definition normal_p ≝ λt. ∀t'. ¬(PTrans t t').


inductive k_closure_c : Crumble → Crumble → Prop ≝
| selfT : ∀c. k_closure_c c c
| recurT : ∀c1, c2, c3. k_closure_c c1 c2 → CTrans c2 c3 → k_closure_c c1 c3
.


(* Se faccio inversion sull'ipotesi kclos mi trovo un IH sbagliata (c2=c3!?), forse sbagliata la definizione?*)

(*
lemma k_closure_wnamed_induction:∀c.
∀c1. k_closure_c c c1 → well_named c=true→ well_named c1 = true.
#c  #c1 #kclos elim kclos
[ //
| #c' #c'' #c''' #kclos2 #ctr #IH #eq1 // destruct
] qed.
*)

(*
definition initial_state ≝ λc. ∃t. ∃s. fresh_var_t t ≤ s ∧ closed_t t
 ∧ fst ? ?(underline_pTerm t s) = c.
*)

definition reachable_Crumble ≝ λc'. ∃c. ∃t. ∃s. fresh_var_t t ≤ s ∧ closed_t t
 ∧ fst … (underline_pTerm t s) = c ∧ k_closure_c c c'.


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

lemma Veo : VEnvironment e0.
@PEpsilon qed.


lemma p_e_to_s : ∀e, s. VEnvironment (Snoc e s) → PracticalSubstitution s.
#e #s #H
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

lemma pract_concat_l : ∀e1, e2. VEnvironment (concat e1 e2) → VEnvironment e1.
@Environment_simple_ind2
[ @Environment_simple_ind2 //
| #e1 #s1 #H1 @Environment_simple_ind2
 [ normalize //
 | #e2 #s2 #H2 normalize #H3 @H2 @(p_e_to_e ? s2) @H3
 ]
] qed.

lemma pract_concat_r : ∀e1, e2. VEnvironment (concat e1 e2) → VEnvironment e2.

@Environment_simple_ind2
[ @Environment_simple_ind2 //
| #e1 #s1 #H1 @Environment_simple_ind2
 [ normalize //
 | #e2 #s2 #H2 #H3 @PSnoc
  [ lapply H3 normalize #H4 @H2 @(p_e_to_e ? s2) @H4
  | lapply H3 normalize #H4 @(p_e_to_s ? ? H4)
  ]
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

lemma p_s_to_b : ∀v, b. PracticalSubstitution (subst v b) → PracticalBite b.
#v #b #H1 inversion H1
#v' #b' #H2 #eq destruct @H2
qed.

lemma p_b_to_v : ∀v. PracticalBite (CValue v) → CPracticalValue v.
#v #H1 inversion H1
#v' #H2 #eq destruct @H2
qed.

lemma pract_ren : ∀b1, e, v, b2, v'.
 VE_Crumble 〈b1, (Snoc e (subst v b2))〉
  → (veqb (ν (fresh_var〈b1, (Snoc e (subst v b2))〉)) v' = true)
   → VE_Crumble 〈b1, (Snoc e (subst v' b2))〉.
#b1 (@Environment_simple_ind2)
[ #v #b2 #v' #H1 #eq @PCCrumble @PSnoc // @Psubst @(p_s_to_b v b2) @(p_e_to_s Epsilon [v←b2]) @(p_ve_to_e b1 (Snoc Epsilon [v←b2])) //
| #e #s #H1 #v #b2 #v' #H2 #veq @PCCrumble @PSnoc
 [ @PSnoc
  [ @(p_e_to_e e s) @(p_e_to_e (Snoc e s) [v←b2]) @(p_ve_to_e b1 (Snoc (Snoc e s) [v←b2])) //
  | @(p_e_to_s e s) @(p_e_to_e (Snoc e s) [v←b2]) @(p_ve_to_e b1 (Snoc (Snoc e s) [v←b2])) // ]
 | @Psubst @(p_s_to_b v b2) @(p_e_to_s (Snoc e s) [v←b2]) @(p_ve_to_e b1 (Snoc (Snoc e s) [v←b2])) // ]
] qed.

lemma pract_ssv : ∀v, y, z. ∀(H: inb_v z v = false). CPracticalValue v → CPracticalValue (ssv v y z H).
*
[ #v #y #z #H #H1 lapply (refl … (var v)) cases H1 in ⊢(? ? ? %→ ?); #v' #c #eq destruct
| #v' #c #y #z #H #H1 whd in ⊢(? %); cases (veqb v' y)
 [ normalize //
 | normalize @Plambda ]
] qed.

lemma pract_sseb : ∀b, y, z. ∀(H: inb_b z b = false). PracticalBite b → PracticalBite (ssb b y z H).
*
[ #v #y #z #H #EP whd in ⊢ (? %); @PValue @pract_ssv @p_b_to_v @EP
| #v1 #v2 #y #z #H #EP whd in ⊢ (? %); inversion EP #H5 #H6 #H7 destruct ]
qed.

lemma pract_at : ∀c1, e2. VE_Crumble c1→ VEnvironment e2 → VE_Crumble (at c1 e2).
* #b1 #e1 #e2 #H0 #H1 normalize @PCCrumble @(pract_env_concat e1 e2)
[ @(p_ve_to_e b1 e1) // | // ]
qed.

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
  [ @(p_e_to_s e ?) @Venv | #Psubst cut (PracticalBite (AppValue v1 v2))
   [ @(p_s_to_b v' ?) @Psubst | #P inversion P #v #CPr #eq destruct ]
  ]
 ]
] qed.


lemma snoc_to_concat: ∀e1, e2, s. Snoc (concat e1 e2) s = concat e1 (Snoc e2 s).
// qed.


lemma witness2: ∀x, e. domb_e x e = true
→ ∃e1, b, e2. e= concat (Snoc e2 (subst x b)) e1.
#x @Environment_simple_ind2
[ normalize #abs cases (? : False) @(absurd (false=true)) // 
| #e * #y #b1 #IH normalize inversion (veqb x y)
 [ #veqt #_ lapply (veqb_true_to_eq x y) * #H1 #_ lapply (H1 veqt) #eq >eq %
  [ @Epsilon | normalize /3/ 
  ]
 | #veqf normalize #domT lapply (IH domT) * #e1 * #b1 * #e2 #eq >eq
   lapply (snoc_to_concat (Snoc e2 [x←b1]) e1 [y←b1]) #eq2 /4/
 ]  
] qed.

lemma domb_veqb_step: ∀x, y, e, b. domb_e x (Snoc e [y←b]) = true
→ veqb y x = false
 → domb_e x e = true.
#x #y #e #b normalize #domt #veqf lapply (veqb_comm y x) #eq destruct lapply domt
<eq >veqf normalize // qed.

lemma domb_snoc: ∀x, e, s. domb_e x (Snoc e s) = false
→ domb_e x e = false.
#x #e * #y #b normalize cases (veqb x y)
[ normalize #abs cases (? : False) @(absurd …abs) //
| normalize // ] qed.

lemma dombf_to_veqf: ∀x, e, y, b. domb_e x (Snoc e [y←b]) = false
→ veqb x y = false.
#x #e #y #b normalize cases (veqb x y)
[ normalize #abs cases (? : False) @(absurd …abs) //
| normalize //
] qed.

lemma myandl: ∀a,b. andb a b = true → a = true.
/2/ qed.


lemma myandr: ∀a,b. andb a b = true → b = true.
/2/ qed.


lemma snoc_to_concat2: ∀e3, e2, s. concat (Snoc e3 s) e2 = concat e3 (concat (Snoc Epsilon s) e2).
//
qed.

lemma well_named_to_dist_dom: ∀b, e. well_named 〈b, e〉 = true
→ dist_dom e = true.
#b #e normalize inversion (well_named_b b)
[ #wnbt inversion (well_named_e e)
 [ #wnet normalize //
 | normalize #_ #abs cases (? : False) @(absurd …abs) //
 ]
| normalize #_ #abs cases (? : False) @(absurd …abs) //
] qed.


lemma concat_to_push :∀e, s. concat (Snoc Epsilon s) e = push e s.
@Environment_simple_ind2
[ #s normalize //
| #e #s #HI #t normalize >HI //
] qed.

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

lemma norm_step: ∀b1, e1, b2, e2, cc, x. 〈b1, e1〉 = plug_c cc 〈b2, e2〉
→ e1 = concat (Snoc Epsilon [x← b2]) e2
 → normal_c 〈b1, e1〉
  → normal_c 〈b2, e2〉.
#b1 #e1 #b2 #e2 *
[ #x #eq1 #eq2 #norm cases (? : False) lapply eq1 normalize destruct #eq2 destruct /2/
| #b' * #e' #y #x #eq1 #eq2 #norm whd in match (normal_c ?); * #b3 #e3 lapply norm
  whd in match (normal_c ?); #norm1 @nmk #ctr inversion ctr
 [ #c1 #c2 #tctr #eq3 #eq4 destruct lapply (closure_step ? ? (crc b' (envc e' y)) tctr) #cctr
   lapply (clos_step ? ? cctr) <eq1 #ctrTrue lapply (norm1 (plug_c (crc b' (envc e' y)) 〈b3,e3〉))
   #ctrFalse @(absurd ? ctrTrue ctrFalse)
 | #c1 #c2 #cctr #eq3 #eq4 destruct inversion cctr * #b1' #e1' * #b2' #e2' *
  [ #tctr normalize #eq2 #eq3 destruct lapply (closure_step ? ? (crc b' (envc e' y)) tctr)
    #cctr lapply (clos_step ? ? cctr) <eq1 #ctrTrue lapply (norm1 (plug_c (crc b' (envc e' y)) 〈b2',e2'〉))
    #ctrFalse @(absurd ? ctrTrue ctrFalse)
  | #b3 * #e3 #z #tctr normalize #eq2 #eq3 lapply eq1 >eq2 whd in match (plug_c ? ?);
    whd in match (plug_e ? ?); lapply (comm_concat (Snoc e' [y←b3]) (Snoc e3 [z←b1']) e1') #eq_concat
    >eq_concat normalize #eq4 lapply (closure_step ? ? (crc b' (envc (concat (Snoc e' [y←b3]) e3) z)) tctr)
    #cctr2 lapply (clos_step ? ? cctr2) normalize <eq4 #ctrTrue
    lapply (norm1 〈b',concat (Snoc (concat (Snoc e' [y←b3]) e3) [z←b2']) e2'〉) #ctrFalse
    @(absurd ? ctrTrue ctrFalse)
  ]
 ]
] qed.

lemma norm_app_value: ∀v1, v2, e. normal_c 〈AppValue v1 v2, e〉
→ closed_c 〈AppValue v1 v2, e〉
 → VEnvironment e
  → False.
*
[ #v' #v2 #e #norm #clos #VEnv lapply (witness v' e ? VEnv)
 [ lapply clos whd in match (closed_c); normalize #clos1 lapply (clos1 v')
   lapply (veqb_true v') #veq >veq cases (domb_e v'e)
  [ // | normalize // ]
 | * #y #wit lapply norm whd in match (normal_c ?); #norm1
   lapply (norm1 (CCrumble (AppValue y v2) e)) #nctr
   lapply (sub_t v' v2 y e VEnv ? wit)
  [ lapply clos whd in match (closed_c); normalize #clos1 lapply (clos1 v')
    lapply (veqb_true v') #veq >veq cases (domb_e v'e)
    [ // | normalize // ]
  | #ctr @(absurd ? (top_step … ctr) nctr)
  ]
 ]
| #x * #b #e #v2 #ev #norm #clos #VEnv lapply norm whd in match (normal_c ?); #norm1
  lapply (norm1 (at (pi1 … (alpha b (push e [x ← CValue v2]) (fresh_var 〈b,push e [x←CValue v2]〉) ? ) ) ev))
 [ // | #nctr
   lapply (cbeta_v x b e v2 ev VEnv) #ctr @(absurd ? (top_step … ctr) nctr)
 ]
] qed.

lemma pract_plug_to_c : ∀b1, e1, b2, e2, x. V_Crumble (plug_c (crc b2 (envc e2 x)) 〈b1, e1〉)
→ V_Crumble 〈b1, e1〉 ∧ V_Crumble 〈b2, e2〉.
#b1 #e1 #b2 #e2 #c #V_C lapply V_C whd in match (plug_c ? ?); whd in match (plug_e ? ?); #V_C2
%
[ lapply (p_vc_to_e ? ? V_C2 ) #Venv1 @PCrumble
 [ lapply (pract_concat_l ? ? Venv1) #Venv2 lapply (p_e_to_s … Venv2) @p_s_to_b
 | @(pract_concat_r ? ? Venv1)
 ]
| @PCrumble
 [ @(p_vc_to_b ? ? V_C2)
 | lapply (p_vc_to_e ? ? V_C2) #Venv1 lapply (pract_concat_l ? ? Venv1) #Venv2 @(p_e_to_e ? ? Venv2)
 ] 
] qed.

lemma practB_TCT_to_abs: ∀b, e, c'. PracticalBite b
→ TCTrans 〈b, e〉 c'
 → False.
#b #e #c' #P_B #tctr inversion tctr
[ #x #b0 #e0 #v #ev #VEnv #eq1 #eq2 destruct inversion P_B #v0 #P_V #eq1 destruct
| #x #ev #VEnv #dombe #eq1 #eq2 destruct inversion P_B #v #P_V #eq destruct inversion P_V #v #c #eq destruct
| #x #v #v' #ev #VEnv #dombe #eq1 #eq2 #eq3 destruct inversion P_B #v0 #P_V #eq1 destruct 
] qed.

lemma well_named_c_to_b: ∀b, e. well_named 〈b, e〉 = true →
well_named_b b = true.
#b #e normalize inversion (well_named_b b)
[ //
| #wnb normalize //
] qed.

lemma well_named_b_to_v: ∀v. well_named_b (CValue v) = true
→well_named_v v = true.
#v normalize // qed.

lemma well_named_c_to_e: ∀b, e. well_named 〈b, e〉 = true →
well_named_e e = true.
#b #e normalize inversion (well_named_b b)
[ #wnb normalize inversion (well_named_e e)
 [ #wne //
 | #wne normalize #abs cases (? : False) @(absurd …abs) //
 ]
| #wnb normalize #abs cases (? : False) @(absurd …abs) //
] qed.

lemma well_named_e_snoc_s: ∀e, s. well_named_e (Snoc e s) = true →
well_named_s s = true.
#e #s normalize inversion (well_named_e e)
[ #wnt normalize //
| #wnf normalize #abs cases (? : False) @(absurd …abs) //
] qed.

lemma well_named_e_snoc_e: ∀e, s. well_named_e (Snoc e s) = true →
well_named_e e = true.
#e #s normalize inversion (well_named_e e)
[ //
| #wnf normalize #abs cases (? : False) @(absurd …abs) //
] qed.

lemma well_named_s_step: ∀x, b. well_named_s [x←b] = true
→ well_named_b b = true.
#x #b normalize // qed.

lemma well_named_snoc: ∀b, e, s. well_named 〈b, Snoc e s〉 = true
→ well_named 〈b, e〉 = true.
#b #e #s whd in match (well_named ?); inversion (well_named_b b)
[ #wnbt inversion (well_named_e (Snoc e s))
 [ #wnet #distdom whd in match (well_named ?); >wnbt lapply (well_named_e_snoc_e ? ? wnet) #wnt >wnt
   lapply (dist_dom_conservative ? ? distdom) normalize //
 | normalize #_ #abs cases (? : False) @(absurd …abs) //
 ]
| normalize #_ #abs cases (? : False) @(absurd …abs) //
] qed.

lemma well_named_appl: ∀v, v', e. well_named 〈AppValue v v', e〉 = true
→ well_named 〈CValue v, e〉 = true.
#v #v' #e normalize inversion (well_named_v v)
[ #wnv inversion (well_named_v v')
 [ #wnv' normalize //
 | #wnv' normalize #abs cases (? : False) @(absurd …abs) //
 ]
| #wnv normalize #abs cases (? : False) @(absurd …abs) //
] qed.

lemma well_named_appr: ∀v, v', e. well_named 〈AppValue v v', e〉 = true
→ well_named 〈CValue v', e〉 = true.
#v #v' #e normalize inversion (well_named_v v)
[ #wnv normalize //
| #wnv inversion (well_named_v v')
 [ #wnv' normalize #abs cases (? : False) @(absurd …abs) //
 | #wnv' normalize //
 ]
] qed.


lemma well_named_concat_l: ∀e1, e2. well_named_e (concat e1 e2) = true
→ well_named_e e1 = true.
#e1 #e2 #wnc lapply (well_named_concat e2 e1) cases (well_named_e e2)
[ normalize cases (well_named_e e1)
 [ normalize //
 | normalize >wnc #abs cases (? : False) @(absurd …abs) //
 ]
| normalize cases (well_named_e e1)
  normalize >wnc #abs cases (? : False) @(absurd …abs) //
] qed.

lemma well_named_concat_r: ∀e1, e2. well_named_e (concat e1 e2) = true
→ well_named_e e2 = true.
#e1 #e2 #wnc lapply (well_named_concat e2 e1) cases (well_named_e e1)
[ normalize #eq <eq @wnc
| normalize >wnc #abs cases (? : False) @(absurd …abs) //
] qed.

lemma wnamed_eval_step: ∀x, e. well_named 〈CValue (var x), e〉 = true
→ well_named 〈evaluate x e, e〉 = true.
#x @Environment_simple_ind2
[ #wnamed normalize //
| #e * #y #b #IH #wnamed whd in match (evaluate ? ? ); lapply wnamed
  whd in match (well_named ?); inversion (well_named_b (CValue (var x))∧well_named_e (Snoc e [y←b]))
 [ #H1 #H2 lapply (myandr ? ? H1) #wnamed_e lapply (well_named_e_snoc_s ? ? wnamed_e) #wnamed_s
   lapply (well_named_s_step ? ? wnamed_s) #wnamed_b
   inversion (veqb y x)
  [ #veqt whd in match (well_named ?); >wnamed_b >wnamed_e >H2 //
  | #veqf whd in match (well_named ?); whd in match (if false then b else evaluate x e);
    lapply (IH (well_named_snoc ? ? ? wnamed)) whd in match (well_named ?); 
    inversion (well_named_b (evaluate x e)∧well_named_e e)
   [ #wnt #distdom >wnamed_e lapply (myandl ? ? wnt) #wnbt >wnbt @H2
   | normalize #_ #abs cases (? : False) @(absurd …abs) //
   ]
  ]
 | normalize #_ #abs cases (? : False) @(absurd …abs) //
 ]
] qed.

lemma domb_step_true: ∀x, y, e, b. veqb y x = true
→ domb_e x (Snoc e [y←b]) = true
 → dist_dom (Snoc e [y←b]) = true
  → domb_e x e = false.
#x #y #e #b #veqt #domt normalize inversion (domb_e y e)
[ #domt2 normalize #abs cases (? : False) @(absurd …abs) //
| #domf #_ lapply (veqb_true_to_eq y x) * #H1 #_ lapply (H1 veqt) #eq <eq @domf
] qed.

lemma wnamed_evaluate: ∀x, e. well_named 〈(CValue (var x)), e〉 = true
→ domb_e x e = true
 → well_named 〈evaluate x e, e〉 =  true.
#x @Environment_simple_ind2
[ //
| #e * #y #b #IH #wnamed #domt normalize inversion (veqb y x)
 [ #veqt >veqt lapply (well_named_s_step ? ? (well_named_e_snoc_s ? ? (well_named_c_to_e ? ? wnamed)))
   #wnb lapply (well_named_e_snoc_e ? ? (well_named_c_to_e ? ? wnamed)) #wne normalize
   >wnb >wne lapply (domb_step_true ? ? ? ? veqt domt (well_named_to_dist_dom ? ? wnamed))
   lapply (veqb_true_to_eq y x) * #H1 #_ lapply (H1 veqt) #eq <eq #domf >domf normalize
   lapply (well_named_to_dist_dom ? ? wnamed) /2/
 | #veqf normalize lapply (IH (well_named_snoc ? ? ? wnamed) (domb_veqb_step ? ? ? ? domt veqf))
   #wnamed2 lapply (well_named_c_to_b ? ? wnamed2) #wnb2 lapply (well_named_c_to_e ? ? wnamed2) #wne2
   >wnb2 >wne2 normalize lapply (dist_dom_s_dom ? ? ? (well_named_to_dist_dom ? ? wnamed)) #domf
   lapply (well_named_s_step ? ? (well_named_e_snoc_s ? ? (well_named_c_to_e ? ? wnamed))) #wnb
   >domf >wnb normalize @(well_named_to_dist_dom ? ? wnamed2)
 ]
] qed.

lemma well_named_build: ∀b, e, x, b'. well_named 〈b, e〉 = true
→ well_named_b b' = true
 → domb_e x e = false
  → well_named 〈b, Snoc e [x←b']〉 = true.
#b #e #x #b' #wnamed #wnb' #domf normalize
>(well_named_c_to_b ? ? wnamed) >(well_named_c_to_e ? ? wnamed) >wnb' >domf >(well_named_to_dist_dom ? ? wnamed) normalize
// qed.

lemma wnamed_evaluate2: ∀x, v, v', e. well_named 〈(AppValue (var x) v), e〉 = true
→ domb_e x e = true
 → evaluate x e = CValue v'
  → well_named 〈AppValue v' v, e〉 =  true.
#x #v #v' @Environment_simple_ind2
[ #wnamed normalize #abs cases (? : False) @(absurd …abs) //
| #e * #y #b #IH #wnamed #domt #eq0 inversion (veqb y x)
 [ #veqt lapply (domb_step_true ? ? ? ? veqt domt (well_named_to_dist_dom ? ? wnamed))
   lapply (veqb_true_to_eq y x) * #H1 #_ lapply (H1 veqt) #eq <eq #domf
   lapply (well_named_c_to_b ? ? (wnamed_evaluate ? ? (well_named_appl ? ? ? wnamed) domt)) >eq0 #wnbv'
   lapply (well_named_b_to_v ? wnbv') #wnv' lapply (well_named_b_to_v ? (well_named_c_to_b ? ? ((well_named_appr ? ? ? wnamed))))
   #wnv lapply (well_named_e_snoc_e ? ? (well_named_c_to_e ? ? wnamed)) #wne
   lapply (well_named_s_step ? ? (well_named_e_snoc_s ? ? (well_named_c_to_e ? ? wnamed))) #wnb
   lapply (well_named_to_dist_dom ? ? (well_named_snoc ? ? ? wnamed)) #disdom normalize
   >wne >wnb >wnv' >wnv >domf >disdom normalize //
 | #veqf lapply (domb_veqb_step  ? ? ? ? domt veqf) #domt2 lapply eq0 whd in match (evaluate ? ?); >veqf
   whd in match (if false then b else evaluate x e); #eq1
   @(well_named_build ? ? ? ? (IH (well_named_snoc ? ? ? wnamed) domt2 eq1) (well_named_s_step ? ? (well_named_e_snoc_s ? ? (well_named_c_to_e ? ? wnamed))) ?)
   lapply (well_named_to_dist_dom ? ? wnamed) normalize inversion (domb_e y e)
  [ #domt normalize #abs cases (? : False) @(absurd …abs) // | // ]
 ]
] qed.




(* ERRORE nella dim: y ∉ u invece che v` *)
(* aggiunto assioma per step p_subst nel caso fvbf, veqf *)
(* LEMMA D.1 *)

lemma D_one: ∀v, v', x. ∃vs. p_subst (val_to_term v) (psubst x (val_to_term v')) = val_to_term vs.
*
[ #y #v' #x inversion (veqb x y)
 [ #veqt lapply (atomic_subst y (val_to_term v')) lapply (veqb_true_to_eq x y) 
   * #Hveq #_ lapply (Hveq veqt) #eq >eq #H1 >H1 % //
 | #veqf lapply (no_subst y x (val_to_term v') veqf) #H1 >H1 % // ]
| #y #u #v' #x inversion (veqb x y)
 [ #veqt lapply (veqb_true_to_eq x y) * #H0 #_ lapply (H0 veqt) #eq >eq
   lapply (no_subst2 x u (val_to_term v')) #eq2 >eq2 % //  
 | inversion (fvb_t y (val_to_term v'))
  [ #fvbt #veqf lapply (abstr_step_subst2 y x u (val_to_term v') fvbt veqf) * #z #eq >eq % // 
  | #fvbf #veqf lapply (abstr_step_subst y x u (val_to_term v') veqf fvbf) #eq >eq % //
  ]
 ]
] qed.

(*LEMMA D.2*)
lemma D_two: ∀n, ev, v'. VEnvironment ev
 → c_size_e ev = n
  → well_named 〈CValue v', ev〉 = true
   → ∃pv'. read_back 〈CValue v', ev〉= val_to_term pv'.
#n @(nat_elim1 n) *
[ #_ *
 [ * #x [ normalize #_ #_ #_ % // | * #b #e #_ #_ #_ % // ] 
 | #e * #v #b #v' #Venv normalize #abs #_ cases (? : False) <(plus_n_Sm) in abs; #abs2 destruct ]
| #m #IH #ev *
 [ #x #Venv inversion (domb_e x ev)
  [ #domT lapply (witness2 x ev domT) * #e2 *  * 
   [ *
    [ #y * #e1 #eq cases (? : False) lapply (p_e_to_s e1 [x←(CValue (var y))] (pract_concat_l ? e2 ?))
     [ <eq @Venv | #ps inversion ps #v #b #pb #eq2 inversion pb #v0 #pv #eq3 inversion pv destruct #v1 #c #eq destruct ]
    | #y #c * #e3 #eq
      >eq #eq2 #wnamed whd in match (read_back ?); whd in match (read_back_b ?)
      >(snoc_to_concat2 e3 e2 [x←CValue (𝛌y.c)])
      >(iper_concat_lemma (concat (Snoc Epsilon [x←CValue (𝛌y.c)]) e2) ? x ?)
     [ >(concat_to_push e2 [x←CValue (𝛌y.c)])
       >(push_lemma) >atomic_subst lapply(IH (c_size_e e2) ? e2 (lambda y c) ? ? ?)
      [ -eq2 -domT -Venv -IH -n -m -eq whd in match (well_named ?); cut (well_named_b (CValue (𝛌y.c)) = true)
       [ @(well_named_s_step ? ? (well_named_e_snoc_s ? ? (well_named_concat_l ? ?(well_named_c_to_e ? ? wnamed))))
       | cut (well_named_e e2 = true)
        [ @(well_named_concat_r ? ?(well_named_c_to_e ? ? wnamed))
        | cut (dist_dom e2 = true)
         [ lapply (dist_dom_concat ? ? (well_named_to_dist_dom ? ? wnamed)) * // | #dd #wne #wnb >dd >wne >wnb // ] ] ]  
      | // | @(pract_concat_r (Snoc e3 [x←(CValue (𝛌y.c))]) e2) <eq @Venv | >size_env_concat in eq2; normalize //
      | * #x0 #H0 % [ @x0 | @H0 ] ]
     | @(dist_dom_s_dom e3 x (CValue (𝛌y.c)))
       lapply (dist_dom_concat (Snoc e3 [x←CValue (𝛌y.c)]) e2) * [ // | @(well_named_to_dist_dom ? ? wnamed) ] ] ]
   | #v1 #v2 * #e1 #eq cases (? : False) lapply (p_e_to_s e1 [x←(AppValue v1 v2)] (pract_concat_l ? e2 ?))
    [ <eq @Venv | #ps inversion ps #v #b #pb #eq2 inversion pb #v0 #pv #eq3 inversion pv #v3 #c #eq4 destruct ] ]
  | #domf #_ #_ whd in match (read_back ? ); %
   [ @(pvar x) | @stronger_aux_read_back3 #y inversion (veqb y x)
    [ #veqt lapply (veqb_true_to_eq y x) * #H1 #_ >(H1 veqt) >domf #abs cases (? : False) @(absurd …abs) //
    | #veqf #domt normalize >veqf normalize // ] ] ]
 | #x * #b #e cases ev
  [ #Venv normalize #abs cases (? : False) @(absurd …abs) // 
  | #e1 * #y * 
   [ #v0 #Venv #csize #wnamed lapply (IH (c_size_e e1) ? e1 (𝛌x.〈b,e〉) ? ? ?)
    [ @(well_named_snoc ? ? ? wnamed) | // | @(p_e_to_e ? ? Venv) | <csize normalize //
    | * #z #eq change with (p_subst ? ?) in match (read_back ?); lapply eq change with (aux_read_back ? ?)
      in match (read_back ?); #eq1 >eq1 whd in match (read_back_b ?); cases v0
     [ #k whd in match (read_back_v ?); @(D_one) | #k * #b2 #e2 whd in match (read_back_v ?); @(D_one) ] ]
   | #v1 #v2 #Venv cases (? : False) lapply (p_e_to_s ? ? Venv) #ps
     lapply (p_s_to_b ? ? ps) #pb inversion pb #v #_ #eq destruct ] ] ]
] qed.

(* LEMMA D.3 *)

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
 [ #domb cut (CTrans c (CCrumble (evaluate x e) e))
  [ destruct @top_step @(sub_var x e VEnv domb)
  | #Trans lapply norm normalize #norm1 lapply (norm1 〈evaluate x e,e〉) #abs elim abs #abs1 lapply (abs1 Trans) #False elim False ]
 | #ndom @(D_three c ? e x ? ? ? eq2 VEnv ? clos wnamed ndom) [ // | // | // | @or_introl @or_intror // ] ]
| #y #c' #e #eq1 #eq2 #VEnv #clos #wnamed #norm destruct @PCrumble
 [ @PValue @Plambda | @VEnv ]
] qed.

(* LEMMA (Corollary) D.4 *)

corollary D_four: ∀c, b, e. c = 〈b, e〉
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


(* PROP 5.3 *)

lemma five_dot_three : ∀e, b. closed_c 〈b, e〉
→ well_named 〈b, e〉 = true
 → ( normal_c 〈b, e〉 ↔ V_Crumble 〈b, e〉).
@Environment_reverse_ind
[ 2: #e' * #x *
 [ 2: #v1 #v2 #IH #b #clos #wnamed %
  [ #norm  @(D_four ? b (concat (Snoc Epsilon  [x←AppValue v1 v2]) e') ? ? clos wnamed norm) // lapply (IH (AppValue v1 v2) ? ?)
   [ @(wnamed_step b x (AppValue v1 v2) e' wnamed)
   | @(clos_step b x (AppValue v1 v2) e' clos)
   | lapply (norm_step b (concat (Snoc Epsilon [x←AppValue v1 v2]) e') (AppValue v1 v2) e' (crc b (envc Epsilon x)) x ? ? norm)
    [ // | normalize // | #norm1 * #norm_to_vc #_ lapply (norm_to_vc norm1) #V_C cases (? : False)
      @(norm_app_value v1 v2 e' norm1 ?)
     [ @(clos_step b x (AppValue v1 v2) e' clos) | @(p_vc_to_e (AppValue v1 v2) e') @V_C ] ] ]
  | #V_C cases (? : False) cut (PracticalBite (AppValue v1 v2))
   [ @(p_s_to_b x) @(p_e_to_s Epsilon) @(pract_concat_l ? e') @(p_vc_to_e b) @V_C
   | #abs inversion abs #v #_ #abs2 destruct ] ] 
 | #v' #IH #b #clos #wnamed %
  [ #norm  @(D_four ? b (concat (Snoc Epsilon  [x←CValue v']) e') ? ? clos wnamed norm) // lapply (IH (CValue v') ? ?)
   [ @(wnamed_step b x (CValue v') e' wnamed)
   | @(clos_step b x (CValue v') e' clos)
   | lapply (norm_step b (concat (Snoc Epsilon [x←CValue v']) e') (CValue v') e' (crc b (envc Epsilon x)) x ? ? norm)
    [ // | normalize // | #norm1 * #norm_to_vc #_ lapply (norm_to_vc norm1) #V_C @pract_env_concat
     [ @PSnoc [ @PEpsilon | @Psubst @PValue @p_b_to_v @(p_vc_to_b (CValue v') e') @V_C ]
     | @(p_vc_to_e (CValue v') e') @V_C ] ] ]
  | #V_C whd in match (normal_c ?); #c' @nmk #ctr inversion ctr
   [ * #b1 #e1 * #b2 #e2 #tctr #eq1 #eq2 destruct @(practB_TCT_to_abs b1 ? 〈b2,e2〉 ? tctr)
     @(p_vc_to_b ? ? V_C)
   | * #b1 #e1 * #b2 #e2 #cctr #eq1 #eq2 inversion cctr * #b1' #e1' * #b2' #e2' *
    [ #tctr #eq3 #eq4 destruct lapply eq3 whd in match (plug_c ? ?); #eq4 lapply tctr
      <eq4 #abs2 @(practB_TCT_to_abs b1 ? 〈b2', e2'〉 ? abs2) @(p_vc_to_b ? ? V_C)
    | #b3 * #e3 #y #tctr normalize #eq3 #eq4 destruct lapply V_C >eq1 #V_C2 lapply (p_vc_to_e ? ? V_C2) #VEnv
      lapply (pract_concat_l ? ? VEnv) #VEnv2 lapply (p_e_to_s ? ? VEnv2) #P_S lapply (p_s_to_b ? ? P_S) #P_B
      @(practB_TCT_to_abs b1' e1' 〈b2',e2'〉 P_B tctr) ] ] ] ]
| 1: #b #clos #wnamed %
 [ #norm @(D_four ? b Epsilon ? ? clos wnamed norm) //
 | #V_C whd in match (normal_c ?); #c' @nmk #ctr inversion ctr 
  [ * #b1 #e1 * #b2 #e2 #tctr #eq1 #eq2 destruct 
    @(practB_TCT_to_abs b1 ? 〈b2, e2〉 ? tctr) @(p_vc_to_b ? ? V_C)
  | * #b1 #e1 * #b2 #e2 #cctr #eq1 #eq2 inversion cctr * #b1' #e1' * #b2' #e2' *
   [ #tctr #eq3 #eq4 destruct lapply eq3 whd in match (plug_c ? ?); #eq4 lapply tctr
     <eq4 #abs2 @(practB_TCT_to_abs b1 ? 〈b2', e2'〉 ? abs2) @(p_vc_to_b ? ? V_C)
   | #b3 * #e3 #y #tctr normalize #eq3 #eq4 destruct lapply V_C >eq1 #V_C2 lapply (p_vc_to_e ? ? V_C2) #VEnv
     lapply (pract_concat_l ? ? VEnv) #VEnv2 lapply (p_e_to_s ? ? VEnv2) #P_S lapply (p_s_to_b ? ? P_S) #P_B
     @(practB_TCT_to_abs b1' e1' 〈b2',e2'〉 P_B tctr) ] ] ]
] qed.



lemma two_dot_one: (∀t. closed_t t
→ normal_p t ↔ ∃v. t = val_to_term v)
∧ (∀v'. closed_tv v'
→ normal_p (val_to_term v') ↔ ∃v. (val_to_term v') = val_to_term v).
@pValueTerm_ind
[ *
 [ #x #_ #clos %
  [ #norm % //
  | #_ cases (? : False) lapply clos whd in match (closed_t ?); #H lapply (H x)
    whd in match (fvb_t ? ?); normalize >(veqb_true x) normalize #abs @(absurd … abs) //
  ]
 | #x #t #_ #clos %
  [ #norm % //
  | #_ whd #t' @nmk #PTrans inversion PTrans
   [ #t0 #u #PTT #eq inversion PTT #v1 #t1 #t2 #eq2 destruct
   | #t0 #u #PCT #eq inversion PCT #t1 #u0 *
    [ #PTT normalize #_ #eq1 #eq2 #eq3 destruct inversion PTT #v1 #t1 #t2 #eq2 destruct
    | #t2 #PTT normalize //
    | #T1 #T2 #PTT normalize *
     [ * #tc #rv #eq2 destruct
     | * #rv #tc #eq2 destruct
     ]
    | #y #T #PTT normalize //
    ]
   ]
  ]
 ] 
| *
 [ *
  [ #x #t #_ #_ #clos %
   [ #norm cases (? :False) lapply (closed_distr ? ? clos) * whd in match (closed_t ?);
     #clos1 #_ lapply (clos1 x) normalize >(veqb_true x) normalize #abs @(absurd …abs) //
   | #abs cases (? :False) lapply abs * #x0 #eq destruct
   ]
  | #x #t #t2 #_ #_ #clos %
   [ whd in match (normal_p ?); #norm cases (? :False) lapply (beta_v x t t2)
     #PT lapply (norm (p_subst t (psubst x t2))) #nPT @(absurd … (top_trans …PT) nPT)
   | * #x0 #abs destruct
   ]
  ]
 | #t1 #t2 #t' #IH1 #IH2 #clos %
  [ whd in match (normal_p ?); #norm cases (? :False) lapply (beta_v x t t2)
  |
  ]
 ]
|
|
] qed.

lemma normal_appl: ∀t, u. normal_p (appl t u)
→ normal_p u.

lemma D_eleven: ∀b,e. closed_c 〈b, e〉
→ well_named 〈b, e〉 = true
 → normal_c 〈b, e〉
  → normal_p (read_back 〈b, e〉).
*
[ #v #e #clos #wnamed #norm
lapply (five_dot_three ? ? clos wnamed) *
#H1 #_ lapply (H1 norm) #VC lapply (D_two (c_size_e e) ? ? (p_vc_to_e ? ? VC) ? wnamed)
 [ // | * #x #eq >eq 
 ]
| #v1 #v2 #e #clos #wnamed #norm lapply (five_dot_three ? ? clos wnamed) * #H1 #_
  cases (?:False) @(norm_app_value ? ? ? norm clos (p_vc_to_e ? ? (H1 norm)))
] qed.

(*
(*TODO*)
lemma wnamed_tctr_step: ∀c1, c2. TCTrans c1 c2
→ well_named c1 = true
 → well_named c2 = true.
* #b1 #e1 * #b2 #e2 #tctr elim tctr
[ #x #b #e #v #ev #VEnv #eq1 @sigma_prop_gen  * #b3 #e3 #eq2 #H1 whd in match (well_named ?); inversion (well_named_b b2∧well_named_e e2)
 [ #H2 normalize (*qua mi serve un lemma per well_named_alpha, *)lapply (w_well_named_alpha b3 e3 (S (fresh_var 〈b3, e3〉))) *
  [ 2: // | #wwnamed #int_dom 
 | 
 ]
| #x #ev #VEnv #domt #wnamed @(wnamed_evaluate ? ? wnamed domt)
| #x #v #v' #ev #VEnv #domt #eq1 #wnamed @(wnamed_evaluate2 ? ? ? ? wnamed domt eq1)
] qed.


lemma wnamed_ctr_step: ∀c1, c2. well_named c1 = true
→ CTrans c1 c2
 → well_named c2 = true.
#c1 #c2 #wnamed #ctr inversion ctr
[ #c10 * #b20 #e20 #tctr #eq1 #eq2 destruct inversion tctr
 [ #x #b #e #v #ev #VEnv #eq1 @sigma_prop_gen #c30 #eq2 #H1 #eq3 <eq3 whd in match (well_named ?); (*TODO*)
 | #x #ev #VEnv #domt #eq1 #eq2 whd in match (well_named ?); lapply wnamed >eq1 #wnamed1
   lapply (wnamed_eval_step ? ? wnamed1) whd in match (well_named ?); inversion (well_named_b (evaluate x ev)∧well_named_e ev)
  [ #wnt //
  | normalize #_ #abs cases (? : False) @(absurd …abs) //
  ] 
 | (*TODO*)
 ]
| (*TODO*)
] qed.



lemma five_dot_five_dot_one: ∀c. reachable_Crumble c
→ well_named c = true.
#c whd in match (reachable_Crumble ?); * #c' * #t * #s #H3 lapply (proj2 … H3) #kclos lapply (proj2 …(proj1… H3))
lapply (proj2 …(proj1 …(proj1… H3))) lapply (proj1 …(proj1 …(proj1… H3))) elim kclos 
[ #c2 #fresh_v #clos #eq1 -H3 lapply (proj1 …four_dot_one_dot_four) #th destruct @(th t s fresh_v)
| #c1 #c2 #c3 #klos1 #CTr #IH #fresh_v #clos #eq1 destruct inversion CTr
 [ #c1 #c2 #tctr #eq1 #eq2 destruct inversion tctr
  [ #x #b #e #v #ev #VEnv #eq1 #eq2 @sigma_prop_gen <eq2 whd in match (pi1 …);
  |
  |
  ]
 |
 ]
] qed.


lemma five_dot_five_two: ∀c. reachable_Crumble c
→ closed_c c.

lemma five_dot_five_three: ∀c. reachable_Crumble c
→

lemma five_dot_five_four: ∀c. reachable_Crumble c

lemma five_dot_five: ∀c. reachable_Crumble c
→ well_named c ∧ closed_c c ∧




*)







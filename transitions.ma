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
(*
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
*)

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
 → TCTrans (CCrumble (AppValue (lambda x (CCrumble b e)) v) ev) (at (pi1 … (alpha b (push e [x ← CValue v]) ? ? ) ) ev)
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


inductive reachable_c : Crumble → Crumble → Prop ≝
| selfT : ∀c. reachable_c c c
| recurT : ∀c, c', c''. reachable_c c c' → CTrans c' c'' → reachable_c c c''
.


definition reachable_Crumble ≝ λc'. ∃t. ∃s. closed_t t
 → reachable_c (match underline_pTerm t s with [ mk_Prod c n ⇒ c]) c'.
 

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
(*
lemma p_b_to_eb : ∀b, v. b = CValue v
→ PracticalBite b
 → EPracticalBite b.
#b #v #eq #H inversion H
(*[*)#v0 #CPVal #eq2 @EPValue @CPVal
(*| #v1 #v2 #_ #_ #eq2 destruct*)
qed.
*)


(*
lemma p_s_to_eb : ∀v, b. PracticalSubstitution (subst v b) → EPracticalBite b.
#v #b #H1 inversion H1
#v' #b' #H2 #eq destruct //
qed.
*)


lemma p_s_to_b : ∀v, b. PracticalSubstitution (subst v b) → PracticalBite b.
#v #b #H1 inversion H1
#v' #b' #H2 #eq destruct @H2
qed.

(*
lemma p_eb_to_v : ∀v. EPracticalBite (CValue v) → CPracticalValue v.
#v #H1 inversion H1 #v' #H2 #eq destruct //
qed.
*)

lemma p_b_to_v : ∀v. PracticalBite (CValue v) → CPracticalValue v.
#v #H1 inversion H1
(*[*) #v' #H2 #eq destruct //
(*| #v1 #v2 #H2 #H3 #eq destruct ]*)
qed.
(*
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
*)
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
(*
lemma pract_ssb : ∀b, y, z. ∀(H: inb_b z b = false). PracticalBite b → PracticalBite (ssb b y z H).
*
[ #val #y #z #H #H1 whd in ⊢ (? %); @PValue @pract_ssv @p_b_to_v //
| #v1 #v2 #y #z #H #H1 whd in ⊢(? %); @PAppValue
 [ @p_b_to_v @PValue @pract_ssv @(p_ab_to_v1 v1 v2) //
 | @p_b_to_v @PValue @pract_ssv @(p_ab_to_v2 v1 v2) //
] qed.
*)
lemma pract_sseb : ∀b, y, z. ∀(H: inb_b z b = false). PracticalBite b → PracticalBite (ssb b y z H).
*
[ #v #y #z #H #EP whd in ⊢ (? %); @PValue @pract_ssv @p_b_to_v @EP
| #v1 #v2 #y #z #H #EP whd in ⊢ (? %); inversion EP #H5 #H6 #H7 destruct ]
qed.

lemma pract_sse : ∀e, y, z. ∀(H: inb_e z e = false). VEnvironment e → VEnvironment (sse e y z H).
@Environment_simple_ind2
[ //
| #e * #v #b #H1 #y #z #H0 #H2 whd in match (sse ? ? ? ?); inversion (veqb y v)
 [ #eq whd in ⊢ (? %); @PSnoc
  [ @H1 @p_e_to_e //
  | @Psubst @pract_sseb @(p_s_to_b v) @(p_e_to_s e) // ]
 | #eq whd in ⊢ (? %); @PSnoc
  [ @H1 @(p_e_to_e e [v←b]) //
  | @Psubst @pract_sseb @(p_s_to_b v) @(p_e_to_s e) // ] ]
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
 | @PSnoc [ // | @Psubst @(p_s_to_b v') @(p_e_to_s e) @(p_ve_to_e b) // ]
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


(*come formalizzare "senza perdita di generalità suppongo y∈fv ecc.."?*)
(*
lemma D_one: ∀v, v', x. ∃vs. p_subst (val_to_term v) (psubst x (val_to_term v')) = val_to_term vs.
*
[ #y #v' #x inversion (veqb x y)
 [ #veqt lapply (atomic_subst y (val_to_term v'))
   lapply (veqb_true_to_eq x y) * #Hveq #_ lapply (Hveq veqt) #eq
   >eq #H1 >H1 % //
 | #veqf lapply (no_subst y x (val_to_term v') veqf) #H1 >H1 % //
 ]
| #y #u #v' #x
] qed.


lemma D_one: ∀v, v', x. is_value_t (p_subst (val_to_term v) (psubst x (val_to_term v'))).
*
[ #y #v' #x inversion (veqb x y)
 [ #veqt lapply (atomic_subst y (val_to_term v'))
   lapply (veqb_true_to_eq x y) * #Hveq #_ lapply (Hveq veqt) #eq
   >eq #H1 >H1 //
 | #veqf lapply (no_subst y x (val_to_term v') veqf) #H1 >H1 //
 ]
| apply (λy. fvb_t y (val_to_term (abstr y u)) #y #u #v' #x cut (fvb_t y (val_to_term (abstr y u)) = false) 
] qed.



lemma D_one: ∀v, v', x. is_value_t v
→ is_value_t v'
 → is_value_t (p_subst v (psubst x v')).
*
[ #v

 [ #v' #x #H1 #H2 cases v
  [ #v1 inversion (veqb x v1)
   [ #veqt lapply (atomic_subst x (val_to_term v'))
    lapply (veqb_true_to_eq x v1) * #Hveq #_ lapply (Hveq veqt) #eq <eq #eq2 >eq2 @H2
   | #veqf lapply (no_subst v1 x (val_to_term v') veqf) #eq >eq normalize //
   ]
  | #y #t inversion (veqb y x)
   [ #veqt lapply (no_subst2 y t (val_to_term v'))
    lapply (veqb_true_to_eq y x) * #Hveq #_ lapply (Hveq veqt) #eq <eq
    #eq2 >eq2 //
   | #veqf lapply (abstr_step_subst y x t (val_to_term v') ? ?)
    [ // | normalize whd in match (free_occ_v ? ?);
   ]
  ]
 |
 ]
|
]
qed.
*)

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
lemma D_two: ∀ev, b, v. VEnvironment ev
→ b = CValue v
 → (∃pv. read_back 〈b, ev〉 = val_to_term pv. ∧
  ∀

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
 [ #domb cut (CTrans c (CCrumble (evaluate x e) e))
  [ destruct @top_step @(sub_var x e VEnv domb)
  | #Trans lapply norm normalize #norm1 lapply (norm1 〈evaluate x e,e〉) #abs elim abs #abs1 lapply (abs1 Trans) #False elim False ]
 | #ndom @(D_three c ? e x ? ? ? eq2 VEnv ? clos wnamed ndom) [ // | // | // | @or_introl @or_intror // ] ]
| #y #c' #e #eq1 #eq2 #VEnv #clos #wnamed #norm destruct @PCrumble
 [ @PValue @Plambda | @VEnv ]
] qed.



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

lemma norm_step: ∀b1, e1, b2, e2, cc, x. 〈b1, e1〉 = plug_c cc 〈b2, e2〉
(*∀b, e, x, b', e'.*) 
→ e1 = concat (Snoc Epsilon [x← b2]) e2
 → normal_c 〈b1, e1〉
  → normal_c 〈b2, e2〉.
#b1 #e1 #b2 #e2(**) *
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

(*
(**) #cc #x #eq1 #eq2 #norm
whd in match (normal_c ?); lapply norm whd in match (normal_c ?); #norm1
#c' lapply (norm1 (plug_c cc c'))(* #nctr @nmk #ctr inversion ctr
[ #c1 #c2 #tctr #eq3 #eq4 lapply (closure_step ? ? cc tctr) #cctr lapply (clos_step ? ? cctr)
  #ctrabs lapply nctr >eq1 >eq3 >eq4 #nctrabs @(absurd … ctrabs nctrabs)
| #c1 #c2 #cctr #eq3 #eq4 destruct inversion cctr #c1' #c2'
  #cc' #tctr #eq2 #eq3 destruct cut (CTrans 〈b1,concat (Snoc Epsilon [x←b']) e2〉 (plug_c cc (plug_c cc' c2')))
 [ >eq1 @clos_step @closure_step 
 |
 ] 
]


*) @not_to_not >eq1 #ctr @clos_step @closure_step inversion ctr
(* scomponi i plug in crumble, dovrebbero ridursi a irriducibili*)
[ //
| #c1 #c2 #cctr #eq3 #eq4 (**) lapply eq1 elim cc
 [ whd in match (plug_c ? ?); #eq5 <eq5 lapply (norm1 c2) >eq5 <eq4 #nctr cases (?:False) @(absurd … ctr (nctr))
 | #b'' * #e'' #y whd in match (plug_c ? ?); whd in match (plug_e ? ?); destruct >eq1
   #eq2  destruct check check  
 ] 

(**)inversion cctr * #b1 #e1 * #b2 #e2 #cc #tctr #eq3 #eq4 destruct elim cc
 [
 | #b'' * #e'' #x normalize
 ]
]
qed. *)


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
  lapply (norm1 (at (pi1 … (alpha b (push e [x ← CValue v2]) ? ? ) ) ev))
 [ 1,2: // | #nctr
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
     [ @(clos_step b x (AppValue v1 v2) e' clos) | @(p_vc_to_e (AppValue v1 v2) e') @V_C ]
    ]
   ]
  | #V_C cases (? : False) cut (PracticalBite (AppValue v1 v2))
   [ @(p_s_to_b x) @(p_e_to_s Epsilon) @(pract_concat_l ? e') @(p_vc_to_e b) @V_C
   | #abs inversion abs #v #_ #abs2 destruct
   ]
  ] 
 | #v' #IH #b #clos #wnamed %
  [ #norm  @(D_four ? b (concat (Snoc Epsilon  [x←CValue v']) e') ? ? clos wnamed norm) // lapply (IH (CValue v') ? ?)
   [ @(wnamed_step b x (CValue v') e' wnamed)
   | @(clos_step b x (CValue v') e' clos)
   | lapply (norm_step b (concat (Snoc Epsilon [x←CValue v']) e') (CValue v') e' (crc b (envc Epsilon x)) x ? ? norm)
    [ // | normalize // | #norm1 * #norm_to_vc #_ lapply (norm_to_vc norm1) #V_C @pract_env_concat
     [ @PSnoc
      [ @PEpsilon | @Psubst @PValue @p_b_to_v @(p_vc_to_b (CValue v') e') @V_C ]
     | @(p_vc_to_e (CValue v') e') @V_C ] 
    ]
   ]
  | #V_C whd in match (normal_c ?); #c' @nmk #ctr inversion ctr
   [ * #b1 #e1 * #b2 #e2 #tctr #eq1 #eq2 destruct @(practB_TCT_to_abs b1 ? 〈b2,e2〉 ? tctr)
     @(p_vc_to_b ? ? V_C)
   | * #b1 #e1 * #b2 #e2 #cctr #eq1 #eq2 inversion cctr * #b1' #e1' * #b2' #e2' *
    [ #tctr #eq3 #eq4 destruct lapply eq3 whd in match (plug_c ? ?); #eq4 lapply tctr
      <eq4 #abs2 @(practB_TCT_to_abs b1 ? 〈b2', e2'〉 ? abs2) @(p_vc_to_b ? ? V_C)
    | #b3 * #e3 #y #tctr normalize #eq3 #eq4 destruct lapply V_C >eq1 #V_C2 lapply (p_vc_to_e ? ? V_C2) #VEnv
      lapply (pract_concat_l ? ? VEnv) #VEnv2 lapply (p_e_to_s ? ? VEnv2) #P_S lapply (p_s_to_b ? ? P_S) #P_B
      @(practB_TCT_to_abs b1' e1' 〈b2',e2'〉 P_B tctr)
    ]
   ]
  ]
 ]
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
     @(practB_TCT_to_abs b1' e1' 〈b2',e2'〉 P_B tctr)
   ]
  ]
 ]
] qed.

lemma five_dot_five_one: ∀c. reachable_Crumble c
→ well_named c.

lemma five_dot_five_two: ∀c. reachable_Crumble c
→ closed_c c.

lemma five_dot_five_three: ∀c. reachable_Crumble c
→

lemma five_dot_five_four: ∀c. reachable_Crumble c

lemma five_dot_five: ∀c. reachable_Crumble c
→ well_named c ∧ closed_c c ∧



lemma D_eight : ∀(t: pTerm). ∀(u: pTerm). ∀(x: Variable). ∀(v : pValue). (*per casi su veqb e fvb_t *)
 PifTrans t u
  → PifTrans (p_subst t (psubst x (val_to_term v))) (p_subst u (psubst x (val_to_term v))).
#t #u #x #v #H1 inversion H1 #v1 #t1 #t2 #eq1 #eq2  lapply (p_subst_distro (val_to_term (abstr v1 t1)) t2 (psubst x (val_to_term v))) #eq3 >eq3
lapply (no_subst2 v1 t1 (val_to_term v))









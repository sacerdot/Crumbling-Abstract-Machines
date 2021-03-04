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

include "arithmetics/nat.ma".

inductive Variable: Type[0] ≝
 | variable: nat → Variable
.

inductive Crumble : Type[0] ≝
 | CCrumble: Bite → Environment → Crumble 
 
with Bite : Type[0] ≝
 | CValue: Value → Bite
 | AppValue: Value → Value → Bite

with Value : Type[0] ≝
 | var : Variable → Value
 | lambda: Variable → Crumble → Value
  
with Environment : Type[0] ≝
 | Epsilon: Environment
 | Snoc: Environment → Substitution → Environment
 
with Substitution: Type[0] ≝
 | subst: Variable → Bite → Substitution
.

inductive pTerm : Type[0] ≝
 | val_to_term: pValue → pTerm
 | appl: pTerm → pTerm → pTerm
 
with pValue : Type[0] ≝
 | pvar: Variable → pValue
 | abstr: Variable → pTerm → pValue
 .
 
inductive pSubst : Type[0] ≝
 | psubst: Variable → pTerm → pSubst
 .

inductive EnvContext: Type [0] ≝
| envc : Environment → Variable → EnvContext
.

inductive CrumbleContext: Type[0] ≝
| hole : CrumbleContext
| crc: Bite → EnvContext → CrumbleContext
.

inductive TermContext : Type[0] ≝ 
| thole : TermContext
| term : pTerm → TermContext
| c_appl : TermContext → TermContext → TermContext
| c_abstr : Variable → TermContext → TermContext
.

inductive CPracticalValue : Value → Prop ≝
| Plambda : ∀ v, c. CPracticalValue (lambda v c)
.

inductive PracticalBite : Bite → Prop ≝
| PValue : ∀v. CPracticalValue v → PracticalBite (CValue v)
| PAppValue : ∀v1, v2. CPracticalValue v1 → CPracticalValue v2 → PracticalBite (AppValue v1 v2)
.

inductive EPracticalBite : Bite → Prop ≝
| EPValue : ∀v. CPracticalValue v → EPracticalBite (CValue v)
.

inductive PracticalSubstitution : Substitution → Prop ≝
| Psubst : ∀v, b. EPracticalBite b → PracticalSubstitution (subst v b)
.

inductive VEnvironment : Environment → Prop ≝
| PEpsilon : VEnvironment (Epsilon)
| PSnoc : ∀e, s. VEnvironment e → PracticalSubstitution s → VEnvironment (Snoc e s)
.

inductive VE_Crumble : Crumble → Prop ≝
| PCCrumble : ∀b, e. VEnvironment e → VE_Crumble (CCrumble b e)
.

inductive V_Crumble : Crumble → Prop ≝
| PCrumble : ∀b, e. PracticalBite b → VEnvironment e → V_Crumble (CCrumble b e)
.

inductive PracticalValue : pValue → Prop ≝
| practAbstr : ∀ v, t. PracticalValue (abstr v t)
.

inductive PracticalTerm : pTerm → Prop ≝
| valT : ∀v. (PracticalValue v → PracticalTerm (val_to_term v))
| applT : ∀t1, t2. (PracticalTerm t1 → PracticalTerm t2 → PracticalTerm (appl t1 t2))
.

notation "[ term 19 v ← term 19 b ]" non associative with precedence 90 for @{ 'substitution $v $b }.
interpretation "Substitution" 'substitution v b =(subst v b).

(*notation "〈 b break, e 〉" non associative with precedence 90 for @{ 'ccrumble $b $e }.
*)
interpretation "Crumble creation" 'pair b e =(CCrumble b e).

notation "𝛌 x . y" right associative with precedence 40 for @{ 'lambda $x $y}.
interpretation "Abstraction" 'lambda x y = (lambda x y ).

notation "ν x" non associative with precedence 90 for @{ 'variable $x}.
interpretation "Variable contruction" 'variable x = (variable x).


lemma test_lambda0: ∀x: Variable. ∀y:Crumble. (𝛌x.y) = (lambda x y).
#x #y normalize // qed.

let rec push e a ≝  
 match e with
 [ Epsilon ⇒ Snoc Epsilon a
 | Snoc e1 a1 ⇒ Snoc (push e1 a) (a1)
 ].
 
let rec e_size e ≝ 
 match e with
 [ Epsilon ⇒ O
 | Snoc e s ⇒ S (e_size e)
 ]
.

let rec pi1ps s on s ≝ 
 match s with [psubst x t ⇒ x] .

let rec pi2ps s on s≝ 
 match s with [psubst x t ⇒ t] .
 
lemma push_test0: Snoc (Snoc Epsilon [ν0 ← CValue (var ν0)]) [ν1 ← CValue (var ν3)] = push ((Snoc Epsilon [ν1 ← CValue (var ν3)])) ([ν0 ← CValue (var ν0)]).
normalize //. qed. 
(*
let rec concat a b ≝ 
 match a with
 [ Epsilon ⇒ b
 | Snoc e a' ⇒ match b with 
                      [ Epsilon ⇒ Snoc e a'
                      | Snoc e' b' ⇒ Snoc (concat e (push e' a')) b'
                      ]
 ].
*)

let rec concat a b on b≝ 
 match b with
 [ Epsilon ⇒ a
 | Snoc b' s ⇒ Snoc (concat a b') s].

let rec plug_e ec c on ec ≝
 match ec with
 [ envc e x ⇒ match c with [ CCrumble b f ⇒ concat (Snoc e [x←b]) f]]
 .

let rec plug_c cc c on c ≝
 match cc with
 [ hole ⇒ c
 | crc b ec ⇒ 〈b, plug_e ec c〉
 ]
.
 
let rec tc_term T on T ≝ 
 match T with
 [ thole ⇒  False
 | term t ⇒ True
 | c_appl t1 t2 ⇒ tc_term t1 ∧ tc_term t2
 | c_abstr c TT ⇒ tc_term TT
 ] .
 
let rec tc_value T on T ≝
 match T with
 [ thole ⇒ False
 | term t ⇒ match t with
   [ val_to_term v ⇒ True
   | appl t1 t2 ⇒ False
   ]
 | c_appl t1 t2 ⇒ False
 | c_abstr x T ⇒ tc_term T
 ]
 .

let rec rv_context T on T ≝
 match T with 
 [ thole ⇒ True
 | term t ⇒ False
 | c_appl t1 t2 ⇒ (tc_term (t1) ∧ rv_context (t2)) ∨ (rv_context (t1) ∧ tc_value (t2))
 | c_abstr x TT ⇒ False
 ]
 .
 
definition plug_E ≝ λE.λD.
 match E with
  [ envc e x ⇒ match D with
    [ hole ⇒ E
    | crc b ec ⇒ match ec with
      [ envc f z ⇒ envc (concat (Snoc e [x ←b]) f) z]
    ]
  ]
.
 
definition plug_C ≝ λC.λD. 
 match C with
 [ hole ⇒ D
 | crc b ec ⇒ crc b (plug_E ec D) 
 ]
 .
 
let rec plug_t T t on T ≝
 match T with
 [ thole ⇒ t
 | term t' ⇒ t'
 | c_appl u1 u2 ⇒ appl (plug_t u1 t) (plug_t u2 t)
 | c_abstr x TT ⇒ val_to_term (abstr x (plug_t TT t))
 ]
 .

let rec plug_T T U on T ≝
 match T with
 [ thole ⇒ U
 | term t' ⇒ term t'
 | c_appl u1 u2 ⇒ c_appl (plug_T u1 U) (plug_T u2 U)
 | c_abstr x TT ⇒ c_abstr x (plug_T TT U)
 ]
 .

lemma concat_test0: concat (Snoc (Snoc Epsilon [ν0 ← CValue (var ν 0)]) [ν1 ← CValue (var \nu 3)]) (Snoc (Snoc Epsilon [ν2 ← CValue (var \nu 3)]) [ν1 ← CValue (var \nu 2)])=
(Snoc (Snoc (Snoc (Snoc Epsilon [ν0 ← CValue (var \nu 0)]) [ν1 ← CValue (var \nu 3)]) [ν2 ← CValue (var \nu 3)]) [ν1 ← CValue (var \nu 2)]).//. qed.

definition at: Crumble → Environment → Crumble ≝ λa,b.
match a with
[ CCrumble bite e  ⇒ CCrumble bite (concat e b) 
].

notation "hvbox(c @ e)" with precedence 35 for @{ 'at $c $e }.
interpretation "@ operation" 'at c e =(at c e).

(*
definition v0: Value ≝ var ν0.
definition b0: Bite ≝ CValue v0.
definition e0: Environment ≝ Epsilon.
definition e1: Environment ≝ Snoc e0 [ν0 ← b0].

definition v1: Value ≝ var \nu 1.
definition e2: Environment ≝ Snoc e0 [ν1 ← b0].

definition c0: Crumble ≝ 〈 b0, e1 〉.
lemma test1:  e2 = e2. // qed.

lemma test2: c0 = CCrumble b0 e1. // qed.

lemma test3: (〈 b0, e1 〉 @ e2) = 〈 b0, concat e1 e2 〉.
// qed.
*)

let rec pTerm_ind (P: pTerm → Prop) (Q: pValue → Prop)
(H1: ?)
(H2: ?)
(H3: ?)
(H4: ?)
(t: pTerm) on t: P t ≝ 
match t return λt. P t with
 [ val_to_term v ⇒ H1 v (pValue_ind P Q H1 H2 H3 H4 v)
 | appl t1 t2 ⇒ H2 t1 t2 (pTerm_ind P Q H1 H2 H3 H4 t1) (pTerm_ind P Q H1 H2 H3 H4 t2)
 ]
 
and pValue_ind (P: pTerm → Prop) (Q: pValue → Prop)
(H1: ?)
(H2: ?)
(H3: ?)
(H4: ?)
(v: pValue) on v: Q v ≝ 
match v return λv. Q v with
 [ pvar x ⇒ H3 x
 | abstr x t ⇒ H4 t x (pTerm_ind P Q H1 H2 H3 H4 t)
 ]
 .
 
lemma pValueTerm_ind: ∀P,Q,H1,H2,H3,H4.
 (∀t. P t) ∧ (∀v. Q v) ≝ 
  λP,Q,H1,H2,H3,H4. conj … (pTerm_ind P Q H1 H2 H3 H4) (pValue_ind P Q H1 H2 H3 H4).
 
 
let rec Crumble_ind (P: Crumble → Prop) (Q: Bite → Prop) (R: Environment → Prop) (S: Value → Prop)
(U: Substitution → Prop)
(H1: ∀b.∀e. Q b → R e → P 〈b, e〉)
(H2: ∀v: Value. S v → Q (CValue v))
(H3: ∀v:Value. ∀w:Value. S v → S w → Q (AppValue v w))
(H4: ∀x. S (var x))
(H5: ∀x: Variable. ∀c: Crumble. P c → S (lambda x c))
(H6: R Epsilon)
(H7: ∀e.∀s. R e →  U s → R (Snoc e s))
(H8: ∀x. ∀b. Q b → U (subst x b))
(c: Crumble)
on c: P c ≝
match c return λc. P c with
[ CCrumble b e ⇒ (H1 b e (Bite_ind P Q R S U H1 H2 H3 H4 H5 H6 H7 H8 b) (Environment_ind P Q R S U H1 H2 H3 H4 H5 H6 H7 H8 e))]

and Bite_ind (P: Crumble → Prop) (Q: Bite → Prop) (R: Environment → Prop) (S: Value → Prop)
(U: Substitution → Prop)
(H1: ∀b.∀e. Q b → R e → P 〈b, e〉)
(H2: ∀v: Value. S v → Q (CValue v))
(H3: ∀v:Value. ∀w:Value. S v → S w → Q (AppValue v w))
(H4: ∀x. S (var x))
(H5: ∀x: Variable. ∀c: Crumble. P c → S (lambda x c))
(H6: R Epsilon)
(H7: ∀e.∀s. R e →  U s → R (Snoc e s))
(H8: ∀x. ∀b. Q b → U (subst x b))
(b: Bite)
on b: Q b ≝
match b return λb. Q b with
[ CValue v ⇒ H2 v (Value_ind P Q R S U H1 H2 H3 H4 H5 H6 H7 H8 v)
| AppValue v w ⇒ H3 v w (Value_ind P Q R S U H1 H2 H3 H4 H5 H6 H7 H8 v) (Value_ind P Q R S U H1 H2 H3 H4 H5 H6 H7 H8 w)
]

and Value_ind (P: Crumble → Prop) (Q: Bite → Prop) (R: Environment → Prop) (S: Value → Prop)
(U: Substitution → Prop)
(H1: ∀b.∀e. Q b → R e → P 〈b, e〉)
(H2: ∀v: Value. S v → Q (CValue v))
(H3: ∀v:Value. ∀w:Value. S v → S w → Q (AppValue v w))
(H4: ∀x. S (var x))
(H5: ∀x: Variable. ∀c: Crumble. P c → S (lambda x c))
(H6: R Epsilon)
(H7: ∀e.∀s. R e →  U s → R (Snoc e s))
(H8: ∀x. ∀b. Q b → U (subst x b))
(v: Value)
on v: S v ≝
match v return λv. S v with
[ var x ⇒ H4 x
| lambda x c ⇒ H5 x c (Crumble_ind P Q R S U H1 H2 H3 H4 H5 H6 H7 H8 c)
]

and Environment_ind (P: Crumble → Prop) (Q: Bite → Prop) (R: Environment → Prop) (S: Value → Prop)
(U: Substitution → Prop)
(H1: ∀b.∀e. Q b → R e → P 〈b, e〉)
(H2: ∀v: Value. S v → Q (CValue v))
(H3: ∀v:Value. ∀w:Value. S v → S w → Q (AppValue v w))
(H4: ∀x. S (var x))
(H5: ∀x: Variable. ∀c: Crumble. P c → S (lambda x c))
(H6: R Epsilon)
(H7: ∀e.∀s. R e →  U s → R (Snoc e s))
(H8: ∀x. ∀b. Q b → U (subst x b))
(e: Environment)
on e: R e ≝ 
match e return λe. R e with
[ Epsilon ⇒ H6
| Snoc e s ⇒ H7 e s (Environment_ind P Q R S U H1 H2 H3 H4 H5 H6 H7 H8 e) (Substitution_ind P Q R S U H1 H2 H3 H4 H5 H6 H7 H8 s)
]

and Substitution_ind (P: Crumble → Prop) (Q: Bite → Prop) (R: Environment → Prop) (S: Value → Prop)
(U: Substitution → Prop)
(H1: ∀b.∀e. Q b → R e → P 〈b, e〉)
(H2: ∀v: Value. S v → Q (CValue v))
(H3: ∀v:Value. ∀w:Value. S v → S w → Q (AppValue v w))
(H4: ∀x. S (var x))
(H5: ∀x: Variable. ∀c: Crumble. P c → S (lambda x c))
(H6: R Epsilon)
(H7: ∀e.∀s. R e →  U s → R (Snoc e s))
(H8: ∀x. ∀b. Q b → U (subst x b))
(s: Substitution)
on s: U s ≝ 
match s return λs. U s with
[subst x b ⇒ H8 x b (Bite_ind P Q R S U H1 H2 H3 H4 H5 H6 H7 H8 b)]
.
 
lemma Crumble_mutual_ind: ∀P,Q,R,S,U,H1,H2,H3,H4,H5,H6,H7,H8.
 (∀c. P c) ∧ (∀b. Q b) ∧ (∀e. R e) ∧ (∀v. S v) ∧ (∀s. U s)≝ 
  λP,Q,R,S,U,H1,H2,H3,H4,H5,H6,H7,H8. conj … (conj … (conj … (conj … 
  (Crumble_ind P Q R S U H1 H2 H3 H4 H5 H6 H7 H8)
  (Bite_ind P Q R S U H1 H2 H3 H4 H5 H6 H7 H8))
  (Environment_ind P Q R S U H1 H2 H3 H4 H5 H6 H7 H8))
  (Value_ind P Q R S U H1 H2 H3 H4 H5 H6 H7 H8))
  (Substitution_ind P Q R S U H1 H2 H3 H4 H5 H6 H7 H8)
  .
 
 
let rec Crumble_ind2 (P: Crumble → Prop) (Q: Bite → Prop) (S: Value → Prop)
(U: Substitution → Prop)
(H1: ∀b.∀e. Q b → P 〈b, e〉)
(H2: ∀v: Value. S v → Q (CValue v))
(H3: ∀v:Value. ∀w:Value. S v → S w → Q (AppValue v w))
(H4: ∀x. S (var x))
(H5: ∀x: Variable. ∀c: Crumble. P c → S (lambda x c))
(H8: ∀x. ∀b. Q b → U (subst x b))
(c: Crumble)
on c: P c ≝
match c return λc. P c with
[ CCrumble b e ⇒ (H1 b e (Bite_ind2 P Q S U H1 H2 H3 H4 H5 H8 b))]

and Bite_ind2 (P: Crumble → Prop) (Q: Bite → Prop) (S: Value → Prop)
(U: Substitution → Prop)
(H1: ∀b.∀e. Q b → P 〈b, e〉)
(H2: ∀v: Value. S v → Q (CValue v))
(H3: ∀v:Value. ∀w:Value. S v → S w → Q (AppValue v w))
(H4: ∀x. S (var x))
(H5: ∀x: Variable. ∀c: Crumble. P c → S (lambda x c))
(H8: ∀x. ∀b. Q b → U (subst x b))
(b: Bite)
on b: Q b ≝
match b return λb. Q b with
[ CValue v ⇒ H2 v (Value_ind2 P Q S U H1 H2 H3 H4 H5 H8 v)
| AppValue v w ⇒ H3 v w (Value_ind2 P Q S U H1 H2 H3 H4 H5 H8 v) (Value_ind2 P Q S U H1 H2 H3 H4 H5 H8 w)
]

and Value_ind2 (P: Crumble → Prop) (Q: Bite → Prop) (S: Value → Prop)
(U: Substitution → Prop)
(H1: ∀b.∀e. Q b → P 〈b, e〉)
(H2: ∀v: Value. S v → Q (CValue v))
(H3: ∀v:Value. ∀w:Value. S v → S w → Q (AppValue v w))
(H4: ∀x. S (var x))
(H5: ∀x: Variable. ∀c: Crumble. P c → S (lambda x c))
(H8: ∀x. ∀b. Q b → U (subst x b))
(v: Value)
on v: S v ≝
match v return λv. S v with
[ var x ⇒ H4 x
| lambda x c ⇒ H5 x c (Crumble_ind2 P Q S U H1 H2 H3 H4 H5 H8 c)
]

and Substitution_ind2 (P: Crumble → Prop) (Q: Bite → Prop) (S: Value → Prop)
(U: Substitution → Prop)
(H1: ∀b.∀e. Q b → P 〈b, e〉)
(H2: ∀v: Value. S v → Q (CValue v))
(H3: ∀v:Value. ∀w:Value. S v → S w → Q (AppValue v w))
(H4: ∀x. S (var x))
(H5: ∀x: Variable. ∀c: Crumble. P c → S (lambda x c))
(H8: ∀x. ∀b. Q b → U (subst x b))
(s: Substitution)
on s: U s ≝ 
match s return λs. U s with
[subst x b ⇒ H8 x b (Bite_ind2 P Q S U H1 H2 H3 H4 H5 H8 b)]
.

lemma Crumble_mutual_ind2: ∀P,Q,S,U,H1,H2,H3,H4,H5,H8.
 (∀c. P c) ∧ (∀b. Q b) ∧ (∀v. S v) ∧ (∀s. U s)≝ 
  λP,Q,S,U,H1,H2,H3,H4,H5,H8. conj … (conj … (conj … 
  (Crumble_ind2 P Q S U H1 H2 H3 H4 H5 H8)
  (Bite_ind2 P Q S U H1 H2 H3 H4 H5 H8))
  (Value_ind2 P Q S U H1 H2 H3 H4 H5 H8))
  (Substitution_ind2 P Q S U H1 H2 H3 H4 H5 H8)
  .

let rec Environment_simple_ind (P: Environment → Prop) (Q: Substitution → Prop) 
(H1: P Epsilon)
(H2: ∀e.∀s. P e → Q s → P (Snoc e s))
(H3: ∀s. Q s)
e on e ≝
 match e return λe. P e with
 [ Epsilon ⇒ H1
 | Snoc e s ⇒ H2 e s (Environment_simple_ind P Q H1 H2 H3 e) (H3 s)
 ].

let rec Environment_simple_ind2 (P: Environment → Prop)
(H1: P Epsilon)
(H2: ∀e.∀s. P e → P (Snoc e s))
e on e ≝
 match e return λe. P e with
 [ Epsilon ⇒ H1
 | Snoc e s ⇒ H2 e s (Environment_simple_ind2 P H1 H2 e)
 ].


let rec reverse_env e on e ≝
match e with
[ Epsilon ⇒ Epsilon
| Snoc e s ⇒ concat (Snoc Epsilon s) (reverse_env e)
].

lemma eps_concat: ∀e. concat Epsilon e = e.
@Environment_simple_ind2
[ normalize //
| #e #s #eq normalize >eq //
] qed.

lemma comm_concat: ∀e1, e2, e3. concat e1 (concat e2 e3) = concat (concat e1 e2) e3.
@Environment_simple_ind2
[ @Environment_simple_ind2
 [ @Environment_simple_ind2
  [ normalize //
  | #e #s #eq normalize lapply (eps_concat e) #eq1 >eq1 >eq1 //
  ]
 | #e #s #H1 @Environment_simple_ind2
  [ normalize //
  | #e' #s' #H2 normalize lapply (eps_concat e) #eq1 >eq1 lapply (eps_concat (concat (Snoc e s) e')) #eq2 >eq2 //
  ]
 ]
| #e #s #H1 @Environment_simple_ind2
 [ @Environment_simple_ind2
  [ normalize //
  | #e' #s' #H2 normalize lapply (eps_concat e') #eq1 >eq1 //
  ]
 | #e' #s' #H2 @Environment_simple_ind2
  [ normalize //
  | #e'' #s'' #H3 whd in match (concat (Snoc e s) (Snoc e' s')); 
    whd in match (concat (Snoc (concat (Snoc e s) e') s') (Snoc e'' s''));
    whd in match (concat (Snoc e s) (concat (Snoc e' s') (Snoc e'' s'')));
    >H3 whd in match (concat (Snoc e s) (Snoc e' s')); //
  ]
 ]
] qed.

lemma rev_concat: ∀e1, e2. reverse_env (concat e1 e2) = concat (reverse_env e2) (reverse_env e1).
@Environment_simple_ind2
[ @Environment_simple_ind2
 [ normalize //
 | #e #s #eq normalize lapply (eps_concat e) #eq2 >eq2 //
 ]
| #e #s #Hind @Environment_simple_ind2
 [ normalize lapply (eps_concat (concat (Snoc Epsilon s) (reverse_env e)))
   #eq' >eq' //
 | #e' #s' #eq normalize >eq lapply (comm_concat (Snoc Epsilon s') (reverse_env e') (reverse_env (Snoc e s)))
   #eq2 >eq2 whd in match (reverse_env (Snoc e s)); //
 ]
] qed.
 

 
lemma rev_env: ∀e. e= reverse_env (reverse_env e).
@Environment_simple_ind2
[ normalize //
| #e #s #eq whd in match (reverse_env (Snoc e s)); lapply (rev_concat (Snoc Epsilon s) (reverse_env e))
  #eq2 >eq2 <eq normalize //
] qed.

theorem Environment_reverse_ind : ∀P: Environment → Prop. 
∀H1: P Epsilon.
∀H2: ∀e.∀s. P e → P (concat (Snoc Epsilon s) e).
∀e. P e.
#P #H1 #H2 #e >(rev_env e) @(Environment_simple_ind2 ? ? ? (reverse_env e))
[  @H1 | normalize #e0 #s @H2 ].
qed.

lemma concat_e_epsilon: ∀e. concat e Epsilon =e.
@Environment_simple_ind2 // qed.

lemma concat_epsilon_e: ∀e. concat Epsilon e=e.
@Environment_simple_ind2 // qed.
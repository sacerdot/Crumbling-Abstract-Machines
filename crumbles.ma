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

(*record variable instead*)

inductive Crumble : Type[0] ≝
 | CCrumble: Byte → Environment → Crumble 
 
with Byte : Type[0] ≝
 | CValue: Value → Byte
 | AppValue: Value → Value → Byte

with Value : Type[0] ≝
 | var : Variable → Value
 | lambda: Variable → Crumble → Value
  
with Environment : Type[0] ≝
 | Epsilon: Environment
 | Cons: Environment → Substitution → Environment
 
with Substitution: Type[0] ≝
 | subst: Variable → Byte → Substitution
.

inductive pifTerm : Type[0] ≝
 | val_to_term: pifValue → pifTerm
 | appl: pifTerm → pifTerm → pifTerm
 
with pifValue : Type[0] ≝
 | pvar: Variable → pifValue
 | abstr: Variable → pifTerm → pifValue
 .
 
inductive pifSubst : Type[0] ≝
 | psubst: Variable → pifTerm → pifSubst
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
 [ Epsilon ⇒ Cons Epsilon a
 | Cons e1 a1 ⇒ Cons (push e1 a) (a1)
 ].
 
let rec e_size e ≝ 
 match e with
 [ Epsilon ⇒ O
 | Cons e s ⇒ S (e_size e)
 ]
.

let rec pi1ps s on s ≝ 
 match s with [psubst x t ⇒ x] .

let rec pi2ps s on s≝ 
 match s with [psubst x t ⇒ t] .
 
lemma push_test0: Cons (Cons Epsilon [ν0 ← CValue (var ν0)]) [ν1 ← CValue (var ν3)] = push ((Cons Epsilon [ν1 ← CValue (var ν3)])) ([ν0 ← CValue (var ν0)]).
normalize //. qed. 

let rec concat a b ≝ 
 match a with
 [ Epsilon ⇒ b
 | Cons e a' ⇒ match b with 
                      [ Epsilon ⇒ Cons e a'
                      | Cons e' b' ⇒ Cons (concat e (push e' a')) b'
                      ]
 ].

lemma concat_test0: concat (Cons (Cons Epsilon [ν0 ← CValue (var ν 0)]) [ν1 ← CValue (var \nu 3)]) (Cons (Cons Epsilon [ν2 ← CValue (var \nu 3)]) [ν1 ← CValue (var \nu 2)])=
(Cons (Cons (Cons (Cons Epsilon [ν0 ← CValue (var \nu 0)]) [ν1 ← CValue (var \nu 3)]) [ν2 ← CValue (var \nu 3)]) [ν1 ← CValue (var \nu 2)]).//. qed.

definition at: Crumble → Environment → Crumble ≝ λa,b.
match a with
[ CCrumble byte e  ⇒ CCrumble byte (concat e b) 
].

notation "hvbox(c @ e)" with precedence 35 for @{ 'at $c $e }.
interpretation "@ operation" 'at c e =(at c e).

definition v0: Value ≝ var ν0.
definition b0: Byte ≝ CValue v0.
definition e0: Environment ≝ Epsilon.
definition e1: Environment ≝ Cons e0 [ν0 ← b0].

definition v1: Value ≝ var \nu 1.
definition e2: Environment ≝ Cons e0 [ν1 ← b0].

definition c0: Crumble ≝ 〈 b0, e1 〉.
lemma test1:  e2 = e2. // qed.

lemma test2: c0 = CCrumble b0 e1. // qed.

lemma test3: (〈 b0, e1 〉 @ e2) = 〈 b0, concat e1 e2 〉.
// qed.

let rec pifTerm_ind (P: pifTerm → Prop) (Q: pifValue → Prop)
(H1: ?)
(H2: ?)
(H3: ?)
(H4: ?)
(t: pifTerm) on t: P t ≝ 
match t return λt. P t with
 [ val_to_term v ⇒ H1 v (pifValue_ind P Q H1 H2 H3 H4 v)
 | appl t1 t2 ⇒ H2 t1 t2 (pifTerm_ind P Q H1 H2 H3 H4 t1) (pifTerm_ind P Q H1 H2 H3 H4 t2)
 ]
 
and pifValue_ind (P: pifTerm → Prop) (Q: pifValue → Prop)
(H1: ?)
(H2: ?)
(H3: ?)
(H4: ?)
(v: pifValue) on v: Q v ≝ 
match v return λv. Q v with
 [ pvar x ⇒ H3 x
 | abstr x t ⇒ H4 t x (pifTerm_ind P Q H1 H2 H3 H4 t)
 ]
 .
 
lemma pifValueTerm_ind: ∀P,Q,H1,H2,H3,H4.
 (∀t. P t) ∧ (∀v. Q v) ≝ 
  λP,Q,H1,H2,H3,H4. conj … (pifTerm_ind P Q H1 H2 H3 H4) (pifValue_ind P Q H1 H2 H3 H4).
 
 
let rec Crumble_ind (P: Crumble → Prop) (Q: Byte → Prop) (R: Environment → Prop) (S: Value → Prop)
(U: Substitution → Prop)
(H1: ∀b.∀e. Q b → R e → P 〈b, e〉)
(H2: ∀v: Value. S v → Q (CValue v))
(H3: ∀v:Value. ∀w:Value. S v → S w → Q (AppValue v w))
(H4: ∀x. S (var x))
(H5: ∀x: Variable. ∀c: Crumble. P c → S (lambda x c))
(H6: R Epsilon)
(H7: ∀e.∀s. R e →  U s → R (Cons e s))
(H8: ∀x. ∀b. Q b → U (subst x b))
(c: Crumble)
on c: P c ≝
match c return λc. P c with
[ CCrumble b e ⇒ (H1 b e (Byte_ind P Q R S U H1 H2 H3 H4 H5 H6 H7 H8 b) (Environment_ind P Q R S U H1 H2 H3 H4 H5 H6 H7 H8 e))]

and Byte_ind (P: Crumble → Prop) (Q: Byte → Prop) (R: Environment → Prop) (S: Value → Prop)
(U: Substitution → Prop)
(H1: ∀b.∀e. Q b → R e → P 〈b, e〉)
(H2: ∀v: Value. S v → Q (CValue v))
(H3: ∀v:Value. ∀w:Value. S v → S w → Q (AppValue v w))
(H4: ∀x. S (var x))
(H5: ∀x: Variable. ∀c: Crumble. P c → S (lambda x c))
(H6: R Epsilon)
(H7: ∀e.∀s. R e →  U s → R (Cons e s))
(H8: ∀x. ∀b. Q b → U (subst x b))
(b: Byte)
on b: Q b ≝
match b return λb. Q b with
[ CValue v ⇒ H2 v (Value_ind P Q R S U H1 H2 H3 H4 H5 H6 H7 H8 v)
| AppValue v w ⇒ H3 v w (Value_ind P Q R S U H1 H2 H3 H4 H5 H6 H7 H8 v) (Value_ind P Q R S U H1 H2 H3 H4 H5 H6 H7 H8 w)
]

and Value_ind (P: Crumble → Prop) (Q: Byte → Prop) (R: Environment → Prop) (S: Value → Prop)
(U: Substitution → Prop)
(H1: ∀b.∀e. Q b → R e → P 〈b, e〉)
(H2: ∀v: Value. S v → Q (CValue v))
(H3: ∀v:Value. ∀w:Value. S v → S w → Q (AppValue v w))
(H4: ∀x. S (var x))
(H5: ∀x: Variable. ∀c: Crumble. P c → S (lambda x c))
(H6: R Epsilon)
(H7: ∀e.∀s. R e →  U s → R (Cons e s))
(H8: ∀x. ∀b. Q b → U (subst x b))
(v: Value)
on v: S v ≝
match v return λv. S v with
[ var x ⇒ H4 x
| lambda x c ⇒ H5 x c (Crumble_ind P Q R S U H1 H2 H3 H4 H5 H6 H7 H8 c)
]

and Environment_ind (P: Crumble → Prop) (Q: Byte → Prop) (R: Environment → Prop) (S: Value → Prop)
(U: Substitution → Prop)
(H1: ∀b.∀e. Q b → R e → P 〈b, e〉)
(H2: ∀v: Value. S v → Q (CValue v))
(H3: ∀v:Value. ∀w:Value. S v → S w → Q (AppValue v w))
(H4: ∀x. S (var x))
(H5: ∀x: Variable. ∀c: Crumble. P c → S (lambda x c))
(H6: R Epsilon)
(H7: ∀e.∀s. R e →  U s → R (Cons e s))
(H8: ∀x. ∀b. Q b → U (subst x b))
(e: Environment)
on e: R e ≝ 
match e return λe. R e with
[ Epsilon ⇒ H6
| Cons e s ⇒ H7 e s (Environment_ind P Q R S U H1 H2 H3 H4 H5 H6 H7 H8 e) (Substitution_ind P Q R S U H1 H2 H3 H4 H5 H6 H7 H8 s)
]

and Substitution_ind (P: Crumble → Prop) (Q: Byte → Prop) (R: Environment → Prop) (S: Value → Prop)
(U: Substitution → Prop)
(H1: ∀b.∀e. Q b → R e → P 〈b, e〉)
(H2: ∀v: Value. S v → Q (CValue v))
(H3: ∀v:Value. ∀w:Value. S v → S w → Q (AppValue v w))
(H4: ∀x. S (var x))
(H5: ∀x: Variable. ∀c: Crumble. P c → S (lambda x c))
(H6: R Epsilon)
(H7: ∀e.∀s. R e →  U s → R (Cons e s))
(H8: ∀x. ∀b. Q b → U (subst x b))
(s: Substitution)
on s: U s ≝ 
match s return λs. U s with
[subst x b ⇒ H8 x b (Byte_ind P Q R S U H1 H2 H3 H4 H5 H6 H7 H8 b)]
.
 
lemma Crumble_mutual_ind: ∀P,Q,R,S,U,H1,H2,H3,H4,H5,H6,H7,H8.
 (∀c. P c) ∧ (∀b. Q b) ∧ (∀e. R e) ∧ (∀v. S v) ∧ (∀s. U s)≝ 
  λP,Q,R,S,U,H1,H2,H3,H4,H5,H6,H7,H8. conj … (conj … (conj … (conj … 
  (Crumble_ind P Q R S U H1 H2 H3 H4 H5 H6 H7 H8)
  (Byte_ind P Q R S U H1 H2 H3 H4 H5 H6 H7 H8))
  (Environment_ind P Q R S U H1 H2 H3 H4 H5 H6 H7 H8))
  (Value_ind P Q R S U H1 H2 H3 H4 H5 H6 H7 H8))
  (Substitution_ind P Q R S U H1 H2 H3 H4 H5 H6 H7 H8)
  .
 
 
let rec Crumble_ind2 (P: Crumble → Prop) (Q: Byte → Prop) (S: Value → Prop)
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
[ CCrumble b e ⇒ (H1 b e (Byte_ind2 P Q S U H1 H2 H3 H4 H5 H8 b))]

and Byte_ind2 (P: Crumble → Prop) (Q: Byte → Prop) (S: Value → Prop)
(U: Substitution → Prop)
(H1: ∀b.∀e. Q b → P 〈b, e〉)
(H2: ∀v: Value. S v → Q (CValue v))
(H3: ∀v:Value. ∀w:Value. S v → S w → Q (AppValue v w))
(H4: ∀x. S (var x))
(H5: ∀x: Variable. ∀c: Crumble. P c → S (lambda x c))
(H8: ∀x. ∀b. Q b → U (subst x b))
(b: Byte)
on b: Q b ≝
match b return λb. Q b with
[ CValue v ⇒ H2 v (Value_ind2 P Q S U H1 H2 H3 H4 H5 H8 v)
| AppValue v w ⇒ H3 v w (Value_ind2 P Q S U H1 H2 H3 H4 H5 H8 v) (Value_ind2 P Q S U H1 H2 H3 H4 H5 H8 w)
]

and Value_ind2 (P: Crumble → Prop) (Q: Byte → Prop) (S: Value → Prop)
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

and Substitution_ind2 (P: Crumble → Prop) (Q: Byte → Prop) (S: Value → Prop)
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
[subst x b ⇒ H8 x b (Byte_ind2 P Q S U H1 H2 H3 H4 H5 H8 b)]
.

lemma Crumble_mutual_ind2: ∀P,Q,S,U,H1,H2,H3,H4,H5,H8.
 (∀c. P c) ∧ (∀b. Q b) ∧ (∀v. S v) ∧ (∀s. U s)≝ 
  λP,Q,S,U,H1,H2,H3,H4,H5,H8. conj … (conj … (conj … 
  (Crumble_ind2 P Q S U H1 H2 H3 H4 H5 H8)
  (Byte_ind2 P Q S U H1 H2 H3 H4 H5 H8))
  (Value_ind2 P Q S U H1 H2 H3 H4 H5 H8))
  (Substitution_ind2 P Q S U H1 H2 H3 H4 H5 H8)
  .
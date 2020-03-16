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

definition max : nat → nat → nat ≝ λa,b. match a with [ O ⇒ b | S n ⇒ match b with [ O ⇒ a | S m ⇒ max n m]].
definition min : nat → nat → nat ≝ λa,b:nat. match a with [ O ⇒ a | S n ⇒ match b with [ O ⇒ b | S m ⇒ min n m]].

(*
inductive term : Type[0] ≝
| BByte: Byte → term
| CrumbledValue: Value → term
| EEnvironment: Environment → term
| CCrumble: Crumble → term

with Byte : Type[0] ≝
 | CValue: Value → Byte
 | AppValue: Value → Value → Byte

with Value : Type[0] ≝
 | Variable: nat → Value
 | Abstraction: Value → Crumble → Value
 
with Environment : Type[0] ≝
 | Epsilon: Environment
 | Abstraction: Environment → Value → Byte → Environment
 
with Crumble : Type[0] ≝
 | CCCrumble: Byte → Environment → Crumble 
.
*)

inductive Crumble : Type[0] ≝
 | CCrumble: Byte → Environment → Crumble 
 
with Byte : Type[0] ≝
 | CValue: Value → Byte
 | AppValue: Value → Value → Byte

with Value : Type[0] ≝
 | var : nat → Value
 | lambda: Value → Crumble → Value
 
with Environment : Type[0] ≝
 | Epsilon: Environment
 | Cons: Environment → Substitution → Environment
 
with Substitution: Type[0] ≝
 | subst: Value → Byte → Substitution
.

notation "[ term 19 v ← term 19 b ]" non associative with precedence 90 for @{ 'substitution $v $b }.
interpretation "Substitution" 'substitution v b =(subst v b).

notation "( b break, e )" non associative with precedence 90 for @{ 'ccrumble $b $e }.
interpretation "Crumble creation" 'ccrumble b e =(CCrumble b e).
(*
notation "λ x . y" right associative with precedence 40 for @{ 'lambda $x $y}.
interpretation "Abstraction" 'lambda x y = (lambda x y ).

lemma test_lambda0: ∀x: Value. ∀y:Crumble. (λx.y) = (lambda x y).
#x #y normalize // qed.
*)

let rec push e a ≝  
 match e with
 [ Epsilon ⇒ Cons Epsilon a
 | Cons e1 a1 ⇒ Cons (push e1 a) (a1)
 ].
 
lemma push_test0: Cons (Cons Epsilon [var 0 ← CValue (var 0)]) [var 1 ← CValue (var 3)] = push ((Cons Epsilon [var 1 ← CValue (var 3)])) ([var 0 ← CValue (var 0)]).
normalize //. qed. 

let rec concat a b ≝ 
 match a with
 [ Epsilon ⇒ b
 | Cons e a' ⇒ match b with 
                      [ Epsilon ⇒ Cons e a'
                      | Cons e' b' ⇒ Cons (concat e (push e' a')) b'
                      ]
 ].

lemma concat_test0: concat (Cons (Cons Epsilon [var 0 ← CValue (var 0)]) [var 1 ← CValue (var 3)]) (Cons (Cons Epsilon [var 2 ← CValue (var 3)]) [var 1 ← CValue (var 2)])=
(Cons (Cons (Cons (Cons Epsilon [var 0 ← CValue (var 0)]) [var 1 ← CValue (var 3)]) [var 2 ← CValue (var 3)]) [var 1 ← CValue (var 2)]).//. qed.

definition at: Crumble → Environment → Crumble ≝ λa,b.
match a with
[ CCrumble byte e  ⇒ CCrumble byte (concat e b) 
].

notation "hvbox(c @ e)" with precedence 35 for @{ 'at $c $e }.
interpretation "@ operation" 'at c e =(at c e).

definition v0: Value ≝ var 0.
definition b0: Byte ≝ CValue v0.
definition e0: Environment ≝ Epsilon.
definition e1: Environment ≝ Cons e0 [v0 ← b0].

definition v1: Value ≝ var 1.
definition e2: Environment ≝ Cons e0 [v1 ← b0].

definition c0: Crumble ≝ ( b0, e1 ).
lemma test1:  e2 = e2. // qed.

lemma test2: c0 = CCrumble b0 e1. // qed.

lemma test3: ((b0, e1) @ e2) = (b0, concat e1 e2).
// qed.
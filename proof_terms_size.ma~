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

inductive list: Type[0] ≝
| nil: list
| cons: nat → list → list
.

let rec length l on l ≝ 
 match l with
 [ nil ⇒ O
 | cons n l ⇒ S (length l)
 ]
 .

let rec lsum (n: nat) : Πl:list. length l = n → nat  ≝
 match n return λn.Πl:list. length l = n → nat with
 [ O ⇒ λ_.λ_.O
 | S m ⇒ λl.
    match l return λl.length l = S m → nat with
    [ nil ⇒ λabs. ?
    | cons x l ⇒ λp.
       x + lsum m l ?
    ]
 ]
 .
[ normalize in abs; destruct
| normalize in p; destruct %
]
qed.

definition mylsum : list → nat ≝ λl. lsum (length l) l (refl …).

let rec sum l on l ≝
 match l with
 [ nil ⇒ O
 | cons x l ⇒ x + sum l
 ]
 .

lemma ala: ∀l: list. mylsum l = sum l .
#l elim l [ normalize // | #x #l1 #Hind normalize normalize in Hind; >Hind //]
qed.


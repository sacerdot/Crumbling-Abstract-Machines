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

inductive tree : Type[0] ≝
 Node : list_tree → tree

with list_tree : Type[0] ≝
   Nil : list_tree
 | Snoc : tree → list_tree → list_tree.

let rec tree_ind
 (P: tree → Prop)
 (Q: list_tree → Prop)
 (H1: ?)
 (H2: ?)
 (H3: ?)
 (t: tree) on t : P t ≝
 match t return λt. P t with
 [ Node l ⇒ H1 l (list_tree_ind P Q H1 H2 H3 l) ]

and list_tree_ind
 (P: tree → Prop)
 (Q: list_tree → Prop)
 (H1: ?)
 (H2: ?)
 (H3: ?)
 (l : list_tree) on l : Q l ≝
 match l return λl. Q l with
 [ Nil ⇒ H2
 | Snoc hd tl ⇒ H3 hd tl (tree_ind P Q H1 H2 H3 hd) (list_tree_ind P Q H1 H2 H3 tl) ].

lemma tree_list_tree_ind:
 ∀P,Q,H1,H2,H3.
  (∀t. P t) ∧ (∀l. Q l)
≝ λP,Q,H1,H2,H3. conj … (tree_ind P Q H1 H2 H3) (list_tree_ind P Q H1 H2 H3).

let rec size_tree t ≝
 match t with
 [ Node l ⇒ S (size_list_tree l) ]

and size_list_tree l ≝
 match l with
 [ Nil ⇒ 0
 | Snoc hd tl ⇒ size_tree hd + size_list_tree tl ].
 
check tree_list_tree_ind. 

lemma foo:
 (∀t. 0 ≤ size_tree t) ∧ (∀l. 0 ≤ size_list_tree l).
 @tree_list_tree_ind
 [ normalize // (* goal 1 *)
 | normalize // (* goal 2 *)
 | #t #t1 #h #h1 normalize // (* goal 3 *)
 ]
qed.

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

include "basics/logic.ma".

inductive And(A,B:Prop) : Prop ≝ 
  conj: A→B→And A B.
  
inductive Or(A,B:Prop) : Prop ≝ 
  or_introl: A→Or A B
| or_intror:B→Or A B.

inductive False:Prop ≝ .

inductive True:Prop ≝ I:True.

inductive ex (A:Type[0]) (Q:A→Prop) : Prop ≝ 
  ex_intro: ∀x:A.Q x → ex A Q.
  

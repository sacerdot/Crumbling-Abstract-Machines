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

inductive nat:Type[0] ≝ 
| O:nat
| S:nat → nat.

let recadd n m ≝
match n with
[ O⇒m 
| S a⇒S(add a m)
].

lemma add_0: ∀a.add a O=a.
#a elim a // normalize
// . qed.

lemma add_S: ∀a,b.add a(S b) =S(add a b).

#a elim a normalize #b // qed.

theorem add_comm: ∀a,b.add a b=add b a.
#a elim a normalize // qed.


include"basics/types.ma".

definition twice ≝ λn.add n n.

theorem ex_half: ∀n.∃m.n=twice m∨n=S(twice m).

#n elim n normalize
[@(ex_intro … O) %1 //

|#x

*
#m

*
#eqx

[@(ex_intro … m) %2 // | @(ex_intro … (S m)) %1 normalize // qed.

include "basics/bool.ma".
include "basics/types.ma".

let rec div2 n ≝ 
match n with
[ O ⇒ 〈O,false〉
| S a ⇒ let 〈q,r〉 ≝ (div2 a) in match r with
                  [ true ⇒ 〈S q,false〉
                  | false ⇒ 〈q,true〉
                  ]
] .


lemma div2SO: ∀n,q.div2 n=〈q,false〉 → div2(S n) =〈q,true〉.
#n #q #eq normalize >eq // qed.

lemma div2S1: ∀n,q.div2 n=〈q,true〉 →div2(S n) =〈S q,false〉.
#n#q#H normalize >H // qed.

let rec nat_of_bool b ≝ 
match b with
[ false ⇒ O
| true ⇒ S O
].


lemma div2_ok: ∀n,q,r.div2 n=〈q,r〉 →n=add(nat_of_bool r) (twice q).

#n elim n 
[ #q #r #H normalize in H; destruct // #n #q#r 
| #x #Hind #q#r
  cut (div2 x = 〈fst …(div2 x), snd …(div2 x)〉) [//]
  cases (snd …(div2 x)) #H
  [ > (div2S1 … H) #H1 destruct normalize @eq_f >add_S @(Hind … H)
  | > (div2SO … H) #H1 destruct normalize @eq_f @(Hind … H)]
  qed.
  
  
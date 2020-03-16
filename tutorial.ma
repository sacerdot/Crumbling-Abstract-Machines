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

include"basics/logic.ma".

check True

inductive bank:Type[0] ≝
| east:bank
| west:bank.

definition opposite ≝ λs. 
match s with
[ east⇒west 
| west⇒east
].

lemma east_to_west: opposite east = west.

normalize.

//qed.

lemma idempotent_opposite: ∀x.opposite (opposite x) = x.

#b

cases b

// qed.

inductive opp :bank→bank→Prop ≝
| east_west: opp east west
| west_east: opp west east.

lemma opp_to_opposite: ∀a,b.opp a b→a = opposite b.

#a
#b
#oppab


cases oppab

//

normalize.

qed.


lemma opposite_to_opp: ∀a,b. a = opposite b → opp a b.

#a
#b
#aoppositeb
>aoppositeb

cases b
//
qed.


record state: Type[0] ≝ 
{ goat_pos:bank
; wolf_pos:bank
; cabbage_pos:bank
; boat_pos:bank
}.

definition start ≝ mk_state east east east east.
definition end ≝ mk_state west west west west.


inductive move:state→state→Prop ≝ 
| move_goat: ∀g,g1,w,c.
  opp g g1 → move(mk_state g w c g) (mk_state g1 w c g1)(* We can move the goat from a bank g to the opposite bank g1if and only if the boat is on the same bank g as the goatand we move the boat along with it. *)
| move_wolf: ∀g,w,w1,c.
  opp w w1→move(mk_state g w c w) (mk_state g w1 c w1)
| move_cabbage: ∀g,w,c,c1.
  opp c c1→move(mk_state g w c c) (mk_state g w c1 c1)
| move_boat: ∀g,w,c,b,b1.
  opp b b1→move(mk_state g w c b) (mk_state g w c b1).
  
inductive safe_state: state→Prop ≝ 
| with_boat:∀g,w,c. safe_state(mk_state g w c g)
| opposite_side:∀g,g1,b. opp g g1→safe_state(mk_state g g1 g1 b).

inductive reachable: state→state→Prop≝
| one:∀x,y.move x y →reachable x y
| more:∀x,z,y.reachable x z→safe_state z→move z y→reachable x y.

lemma problem:reachable start end.

/9/

normalize.

qed.  

lemma problem1: reachable start end.

normalize @ more

[@(mk_state east west west east) || // | /2/ ]

(*
@ (more ? (mk_state east west west west)) /2/

@ (more … (move_wolf …))

[4: @east]*)

@(more … (move_goat west … )) /2/

qed.


inductive nat:Type[0] ≝ 
| O:nat
| S:nat→nat.

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

[@(ex_intro … M) 
@
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

include "crumbles.ma".
include "basics/types.ma".
include "variables.ma".
include "utils.ma".
include "size.ma".
include "libnat.ma".

let rec subst_sig (n: nat) y b': Πc. (sc_size c ≤ n) → 
Σd: Crumble. ((sc_size d = (sc_size c)+ (free_occ y c) * ((sc_size_b b') - 1))) ≝ 
 match n return λn. Πc. (sc_size c ≤ n) → 
  Σd: Crumble. ((sc_size d = (sc_size c)+ (free_occ y c) * ((sc_size_b b') - 1)))
  with
  
[ O ⇒ λc. ?
| S m ⇒ λc. match c return λc. (sc_size c ≤ n) → 
  Σd: Crumble. ((sc_size d = (sc_size c)+ (free_occ y c) * ((sc_size_b b') - 1))) with
  [ CCrumble b e ⇒ λp. mk_Sig … 〈 pi1 … (b_subst_sig m y b' b ?), pi1 … (e_subst_sig m y b' e ?) 〉 ? ]
]

and b_subst_sig (n: nat) y b': Πb. (sc_size_b b ≤ n) →
Σg: Byte. ((sc_size_b g = (sc_size_b b)+ (free_occ_b y b) * ((sc_size_b b') - 1))) ≝

match n return λn. Πb. (sc_size_b b ≤ n) →
Σg: Byte. ((sc_size_b g = (sc_size_b b)+ (free_occ_b y b) * ((sc_size_b b') - 1))) with
[ O ⇒ λb.λp. mk_Sig … b ?
| S m ⇒ λb.λp. mk_Sig … b ?
]


and e_subst_sig (n: nat) y b': Πe. (sc_size_e e ≤ n) →
Σf: Environment. ((sc_size_e f = (sc_size_e e)+ (free_occ_e y e) * ((sc_size_b b') - 1))) ≝ 

match n return λn. Πe. (sc_size_e e ≤ n) →
Σf: Environment. ((sc_size_e f = (sc_size_e e)+ (free_occ_e y e) * ((sc_size_b b') - 1))) 

with
[ O ⇒ λe.λp. mk_Sig … e ?
| S m ⇒ λe.λp. mk_Sig … e ?
]
.
include "arithmetics/nat.ma".
include "basics/types.ma".

lemma persistent_case: ∀n. n = 0 ∨ ∃x. S x=n.
#n cases n
[ % //
| #m cut (∃x. S x= S m) /2/
] qed.

lemma sigma_prop_gen:
 ∀A,P.
  ∀Q: A → Prop.
   ∀c: Σx:A.P x.
   (∀z. z = pi1 ?? c → P z → Q z) →
     Q (pi1 ?? c).
#A #P #Q * /2/
qed.

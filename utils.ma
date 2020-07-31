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

lemma orb_to_prop: ∀b, b'. orb b b' = true → b=true ∨ b' = true.
#b #b' cases b cases b' /2/ 
change with (false) in match (false ∨false); #abs destruct qed.

lemma bool_inverse: ∀(A: Type[0]).∀(B: Type[0]).∀(f: A → bool).∀(g: B → bool).∀(x: A).∀(y: B).
 (f x=true → g y =true) → (g y =false → f x=false).
 
#A #b #f #g #x #y cases f cases g // #H #_ <H // qed. 

lemma orb_false: ∀a,b. orb a b = false → a=false ∧ b=false.
#a #b cases a cases b normalize /2/ qed.

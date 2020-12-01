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

lemma letin_inline:
 ∀A.∀(B:Type[0]).
   ∀P:(B→ Prop).
   ∀(x).
    ∀(y:(A→ B)).
    (∀z.(z=x → P (y z))) →
    P (let (z:A) ≝ x in (y z)).
#A #B #P #x #y #H
normalize @H // qed.

lemma test_lil: (let x≝ plus 2 1 in x+2)=5.
@letin_inline #z #H >H // qed.

lemma bool_impl_inv:
 ∀(A:Type[0]). ∀(B:Type[0]).
  ∀(f: A → bool).
   ∀(g: B → bool).
    ∀x,y,b,d.
     ((g y = ¬ d) → (f x = ¬ b)) →
      (f x = b → g y = d).
#A #B #f #g #x #y #b #d cases b cases d cases g // normalize cases f //
#H #_ >H // qed.

lemma bool_impl_inv2:
 ∀(A:Type[0]). ∀(B:Type[0]). ∀(C:Type[0]). ∀(D:Type[0]).
  ∀(f: A → B → bool).
   ∀(g: C → D → bool).
    ∀x,y,z,w,b,d.
     ((g y z = ¬ d) → (f x w = ¬ b)) →
      (f x w = b → g y z = d).
#A #B #C #D #f #g #x #y #z #w #b #d cases b cases d cases g // normalize cases f //
#H #_ >H // qed.

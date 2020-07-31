include "basics/types.ma".
include "arithmetics/nat.ma".
include "crumbles.ma".

let rec t_size t on t ≝
 match t with
 [ val_to_term v ⇒ v_size v
 | appl t1 t2 ⇒ S ((t_size t1) + (t_size t2))
 ]

and v_size v on v ≝
 match v with
 [ pvar v ⇒ 1
 | abstr x t ⇒ S (t_size t)
 ]
.

lemma pif_size_not_zero: (∀t. t_size t ≥ O) ∧ (∀v. v_size v ≥ O).
@pifValueTerm_ind
[ #v #H normalize /2/
| #t1 #t2 #H1 #H2 /2/
| #x normalize //
| #t #x #H normalize //
]
qed.

let rec sc_size c on c ≝
 match c with
 [ CCrumble b e ⇒ S (sc_size_b b + sc_size_e e) ]

and

sc_size_b b on b ≝
 match b with
 [ CValue v ⇒ S (sc_size_v v)
 | AppValue v w ⇒ S (sc_size_v v + sc_size_v w)
 ]

and

sc_size_e e on e ≝
 match e with
 [ Epsilon ⇒ O
 | Cons e s ⇒ (sc_size_e e) + sc_size_s s
 ]

and

sc_size_v v on v ≝
 match v with
 [ var x ⇒ S O
 | lambda x c ⇒ S (sc_size c)
 ]

and

sc_size_s s on s ≝
 match s with
 [ subst x b ⇒ S (sc_size_b b)]
 .
 
let rec c_size c on c ≝
 match c with
 [ CCrumble b e ⇒ (c_size_b b + c_size_e e) ]

and

c_size_b b on b ≝
 match b with
 [ CValue v ⇒ c_size_v v
 | AppValue v w ⇒ S (c_size_v v + c_size_v w)
 ]

and

c_size_e e on e ≝
 match e with
 [ Epsilon ⇒ O
 | Cons e s ⇒(c_size_e e) + c_size_s s
 ]

and

c_size_v v on v ≝
 match v with
 [ var x ⇒ S O
 | lambda x c ⇒ S (c_size c)
 ]

and

c_size_s s on s ≝
 match s with
 [ subst x b ⇒ S (c_size_b b)]
 .

lemma size_env_push: ∀e, s. c_size_e (Cons e s) = c_size_e (push e s).
#e #s
@(Environment_simple_ind2 … e)
[normalize //
| #e' #s' #H whd in match (push ? ?);
  change with (c_size_e (Cons e' s')+ c_size_s s) in match (c_size_e (Cons (Cons e' s') s));
  change with (c_size_e (push e' s)+ c_size_s s') in match (c_size_e (Cons (push e' s) s'));
  <H normalize //
] qed.

lemma size_env_concat: ∀e', e. c_size_e (concat e e') = c_size_e e + c_size_e e' .
@(Environment_simple_ind2)
[ normalize //
| #e1 #s #H #e  cases e [ normalize >(concat_epsilon_e e1) //] #e'' #s' normalize
  >(H (Cons e'' s')) normalize //
] qed.


lemma t_size_gt_O: (∀t. t_size t > 0) ∧
                     (∀v. v_size v > O).

@pifValueTerm_ind
[ #v #H1 normalize in H1; normalize @H1
| #t1 #t2 normalize #H1 #H2  /2/
| #x normalize //
| #t #x normalize #H1 cases (t_size t)[ // | #n /2/]
] qed.

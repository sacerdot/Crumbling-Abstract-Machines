
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



(*

 Componenti del gruppo (completare):

 * Nome1: ...
 * Cognome1: ...
 * Numero di matricola1: ...

 * Nome2: ...
 * Cognome2: ...
 * Numero di matricola2: ...

*)

(* Saltate le righe seguenti dove vengono dati gli assiomi e definite
   le notazioni e cercate Exercise 1. *)

include "basics/logic.ma".
include "basics/core_notation.ma".

notation "hvbox(A break ⇔ B)" left associative with precedence 30 for
@{'iff $A $B}.
interpretation "iff" 'iff A B = (iff A B).

(* set, ∈ *)
axiom set: Type[0].
axiom mem: set → set → Prop.
axiom incl: set → set → Prop.

notation "hvbox(a break ∈ U)" non associative with precedence 50 for
@{'mem $a $U}.
interpretation "mem" 'mem = mem.

notation "hvbox(a break ⊆ U)" non associative with precedence 50 for
@{'incl $a $U}.
interpretation "incl" 'incl = incl.

(* Extensionality *)
axiom ax_extensionality: ∀A, B. (∀Z. Z ∈ A ⇔ Z ∈ B) → A = B.

(* Inclusion *)
axiom ax_inclusion1: ∀A, B. A ⊆ B → (∀Z. Z ∈ A → Z ∈ B).
axiom ax_inclusion2: ∀A, B. (∀Z. Z ∈ A → Z ∈ B) → A ⊆ B.

(* Emptyset  ∅ *)
axiom emptyset: set.

notation "∅" non associative with precedence 90 for @{'emptyset}.
interpretation "emptyset" 'emptyset = emptyset.

axiom ax_empty: ∀X. (X ∈ ∅)→ False.

(* Intersection ∩ *)
axiom intersect: set → set → set.

notation "hvbox(A break ∩ B)" left associative with precedence 80 for
@{'intersect $A $B}.
interpretation "intersect" 'intersect = intersect.

axiom ax_intersect1: ∀A,B. ∀Z. (Z ∈ A ∩ B → Z ∈ A ∧ Z ∈ B).
axiom ax_intersect2: ∀A,B. ∀Z. (Z ∈ A ∧ Z ∈ B → Z ∈ A ∩ B).

(* Union ∪ *)
axiom union: set → set → set.

notation "hvbox(A break ∪ B)" left associative with precedence 70 for
@{'union $A $B}.
interpretation "union" 'union = union.

axiom ax_union1: ∀A,B. ∀Z. (Z ∈ A ∪ B → Z ∈ A ∨ Z ∈ B).
axiom ax_union2: ∀A,B. ∀Z. (Z ∈ A ∨ Z ∈ B → Z ∈ A ∪ B).

notation "'ABSURDUM' A" non associative with precedence 89 for @{'absurdum $A}.
interpretation "ex_false" 'absurdum A = (False_ind ? A).

(* Da qui in avanti riempite i puntini e fate validar quello che scrivete
   a Matita usando le icone con le frecce. *)

(* Exercise 1 *)
theorem union_inclusion: ∀A, B. A ⊆ A ∪ B.
 #A
 #B
 cut (∀z. z ∈ A → z ∈ A ∪ B)
 [#z
 #ZinA
 cut (z \in A ∨ z \in B) [ %1 // |
 #H @ax_union2 @H] |
 #H @ax_inclusion2 @H qed.

(* Exercise 2 *)
theorem union_idempotent: ∀A. A ∪ A = A.
 #A
 cut (∀e. e ∈ A ∪ A ↔ e ∈ A)
 [ normalize #e %1 [ #H
 cut ((e ∈ A ∨ e ∈ A)→ e ∈ A)
 [ #H1 cases H1 [ // | //]
 | #H1 @H1 @ax_union1 @H]
 | #H @ax_union2 % //]
 |
 #H @ax_extensionality @H qed.

(* Exercise 3 *)
theorem intersection_idempotent: ∀A. A ∩ A = A.
#A
 cut (∀z. z ∈ A ∩ A ↔ z ∈ A)
 [#z normalize %1 [ #H
 cut (z ∈ A ∧ z ∈ A)
 [ @ax_intersect1 @H
 | #H1 elim H1 //]
 | #H @ax_intersect2 % //
 ]
 | #H @ax_extensionality
 @H qed.


(* Exercize 4 *)
theorem empty_absurd: ∀X, A. X ∈ ∅ → X ∈ A.
#X #A #H
cut (False)
[ lapply H @ax_empty | #F cases F] qed.

(* Exercise 5 *)
theorem intersect_empty: ∀A. A ∩ ∅ = ∅.
#A
cut (∀z. z ∈ A ∩ ∅ ↔ z ∈ ∅)
#Z
[ normalize %1[ #H 
 cut (Z ∈ A ∧ Z ∈ ∅)
 [ @ax_intersect1 @H] #H1 elim H1 // |
 #H cut (False)
 [lapply H @ax_empty] #F cases F ] |@ax_extensionality @Z
 qed.
 
theorem union_empty: ∀A. A ∪ ∅ = A.
#A
cut (∀z. z \in A ∪ ∅ \harr z ∈ A )
[ #z normalize %1
[ #H cut (z ∈A ∨z ∈ ∅) [ @ax_union1 @H
| #H1 cases H1 [// | #F cut (False) [ lapply F @ax_empty | #FF cases FF]
] ] | @ax_inclusion1 //] | @ax_extensionality qed.

(* Exercise 7 *)

theorem intersect_commutative: ∀A,B. A ∩ B = B ∩ A.
#A #B
cut (∀z. z ∈ A ∩ B ↔ z ∈ B ∩ A )
[ #z normalize %1 [#H
cut (z ∈ B ∧ z ∈ A)[2: @ax_intersect2 | 1: %
[cut (z ∈ A ∧ z ∈ B) lapply H [@ax_intersect1 | #H7 #H8 elim H8 #H10 #H11 @H11]
| cut (z ∈ A ∧ z ∈ B) lapply H [@ax_intersect1 | #H13 #H14 elim H14 //]]
]| #H cut (z ∈ B ∧ z ∈ A)[ lapply H @ax_intersect1 | #H1 @ax_intersect2 elim H1 #H16 #H17 % //]
]| @ax_extensionality qed.  

(* Exercise 8 *)
theorem union_commutative: ∀A,B. A ∪ B = B ∪ A.
#A #B
cut (∀z. z ∈ A ∪ B ↔ z ∈ B ∪ A)
[ #z normalize %1 [#H cut (z ∈ A ∨ z ∈ B) [ lapply H @ax_union1 | #H1
cut (z ∈ B ∨ z ∈ A) [ cases H1 [ #ZA @or_intror // | #ZB @or_introl //] | @ax_union2]]
| #H cut (z ∈ B ∨ z ∈ A) [ lapply H @ax_union1 | #H1
cut (z ∈ A ∨ z ∈ B) [ cases H1 [ #ZA @or_intror // | #ZB @or_introl //] | @ax_union2]]]
| @ax_extensionality ] qed.

(* Exercise 9 *)
theorem distributivity1: ∀A,B,C. A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C).
#A #B #C
cut (∀z. z ∈ A ∪ B ∩ C ↔ z ∈ (A ∪ B) ∩ (A ∪ C))
[2: #H @ax_extensionality @H
| 1: #z normalize %1
[ #H cut (z ∈ A ∪ B ∧ z ∈ A ∪ C)
[ cut (z ∈ A ∨ z ∈ B \cap C) [ lapply H @ax_union1 | #H2 cases H2 [ #H3 %1 @ax_union2 @or_introl //]]
#H3 % [ cut (z ∈ B ∧ z ∈ C) [ lapply H3 @ax_intersect1 | #H4  elim H4 #H5 #H6 cut (z ∈ A  ∨ z ∈ B) [ @or_intror //
| @ax_union2]]] cut (z ∈ B ∧ z ∈ C) [ lapply H3 @ax_intersect1 | #H4 elim H4 #H5 #H5 cut (z ∈ A ∨ z ∈ C) [ @or_intror //
| @ax_union2]] | @ax_intersect2]
| 
 #H cut (z ∈ A ∪ B ∧ z ∈ A ∪ C) [ lapply H @ax_intersect1 |#H1 cut ((z ∈ A ∨ z ∈ B) ∧ (z ∈  A ∨ z ∈ C))
 [ elim H1 #H2 #H3 %1[ lapply H2 @ax_union1 | lapply H3 @ax_union1 ] |
 #H2 cut (z ∈ A ∨ z ∈ B ∩ C) [ elim H2 #H3 #H4 cases H3 [cases H4 [ #H29 #H30 @or_introl //| #H32 #H33 @or_introl //]
| cases H4 [ #H41 #H42 @or_introl // | #H44 #H45 @or_intror cut (z ∈ B ∧ z ∈ C) [ % //] @ax_intersect2]]| @ax_union2   ]]
]]]qed.
(* Exercise 10 *)
theorem distributivity2: ∀A,B,C. A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C).
#A #B #C
cut (∀z. z ∈ A ∩ (B ∪ C) ↔ z ∈ A ∩ B ∪ A ∩ C)
[ 2: @ax_extensionality
| #z normalize %1
  [ #H cut (z ∈ A ∧ z ∈ (B ∪ C))
    [ lapply H @ax_intersect1
    | cut (z ∈ A ∧ (z ∈ B ∨ z ∈ C))
      [ %
        [ cut (z ∈A ∧ z ∈ (B ∪ C))
          [ lapply H @ax_intersect1
          | #H1 elim H1 //]
        | cut (z ∈ B ∪ C)
          [ cut (z ∈ A ∧ z ∈ (B ∪ C))
            [ lapply H @ax_intersect1
            | #H1 elim H1 //]
      | @ax_union1]
      ]
    | #H1 #H2 cut ((z ∈ A ∩ B) ∨ (z ∈ A ∩ C))
      [ elim H1 #H3 #H4 cases H4
        [ #H5 @or_introl cut (z ∈ A ∧ z ∈ B)
          [ /2/ | @ax_intersect2]
        | #H5 @or_intror cut (z ∈ A ∧ z ∈ C)
          [ /2/ | @ax_intersect2]
        ]
      | #H3 @ax_union2 @H3]
    ]
  ]
| #H cut (z ∈ A ∩ B ∨ z ∈ A ∩ C)
  [ lapply H @ax_union1
  | #H1 cut ( z ∈ A ∧ z ∈ B ∨ z ∈ A ∧ z ∈ C)
    [ cases H1
      [ #H2 @or_introl lapply H2 @ax_intersect1
      | #H2 @or_intror lapply H2 @ax_intersect1]
    | #H2 cut (z ∈ A ∧z ∈ (B ∪ C))
      [ %1
        [ elim H2 #H3 cases H3 //]
      | @ax_intersect2]
    ]
  ]
] cases H2 #H3 elim H3 #H4 #H5 [ cut (z ∈ B ∨ z ∈ C)
 [ @or_introl //] | cut(z ∈B ∨ z ∈ C) [ @or_intror // | @ax_union2 ]] @ax_union2
 ]qed.


(********** Inizio degli esercizi del laboratorio 2 *******************)

(* Exercise 11 *)
theorem antisymmetry_inclusion: ∀A,B. A ⊆ B → B ⊆ A → A = B.
#A #B
#H1 #H2
cut (∀z. z ∈ A ↔ z ∈ B)
  [ #z normalize %1
    [ @ax_inclusion1 @H1
    | @ax_inclusion1 @H2
    ]
  | @ax_extensionality
  ]
qed.

(* Exercise 12 *)
theorem reflexivity_inclusion: ∀A. A ⊆ A.
#A
cut (∀z. z ∈ A → z ∈ A)
  [ #z //
  | #H @ax_inclusion2 /2/
  ]
qed.

(* Exercise 13 *)
theorem transitivity_inclusion: ∀A,B,C. A ⊆ B → B ⊆ C → A ⊆ C.
#A #B #C
#H1 #H2
cut (∀z. z ∈ A → z ∈ C)
  [  #z cut (∀z. z ∈ A → z ∈ B)
    [ #z1 @ax_inclusion1 @ H1
    | #H3 cut (∀z. z ∈ B →  z ∈ C)
      [ #z1 @ax_inclusion1 @H2
      | #H4 cut (∀z. z ∈ A → z ∈ C)
          [ #z1 #H5 /3/
          | #H5 @ax_inclusion1 lapply H5 @ax_inclusion2
          ]
      ]
    ]
  | @ax_inclusion2
  ]
qed. 


(************ POWERSET ***************)
axiom powerset: set → set.

axiom ax_powerset1: ∀A. ∀Z. (Z ∈ powerset A → Z ⊆ A).
axiom ax_powerset2: ∀A. ∀Z. (Z ⊆ A → Z ∈ powerset A).

(* Exercise 14 *)
theorem powerset_emptyset: ∀A. A ∈ powerset ∅ → A = ∅.
#A #H
cut (A \subseteq ∅)
  [ lapply H @ax_powerset1
  | #H1 cut (∅ ⊆ A)
    [ cut (∀z. z ∈ ∅ → z ∈ A)
      [ #z @empty_absurd
      | @ax_inclusion2
      ]
     | #H2 cut (∀ z. z ∈ A ↔ z ∈ ∅)
        [ #z normalize %1
          [ @ax_inclusion1 @H1
          | @ax_inclusion1 @H2
          ]
        | @ax_extensionality
        ]
    ]
  ]
qed.

(* Exercise 15 *)
theorem union_powerset: ∀A, B. (powerset A) ∪ (powerset B) ⊆ powerset (A ∪ B).
#A #B
cut (∀z. z ∈ (powerset A) ∪ (powerset B) → z ∈ (powerset (A ∪ B)))
  [ #z #H cut (z ∈ (powerset A) ∨ z ∈ (powerset B))
    [ lapply H @ax_union1 
    | #H1 cases H1
      [ #H2 cut (z ⊆ A)
        [ @ax_powerset1 @H2
        | #H3 cut (z \subseteq A ∪ B)
          [ lapply H3 cut (∀X. X ⊆ A → X ⊆ A ∪ B)
            [ #X #H4 cut (∀x. x ∈ A → x ∈ A ∪ B)
              [ #x #H5 cut (x ∈ A ∨ x ∈ B)
                [ @or_introl //
                | @ax_union2
                ]
              | #H5 cut (X ⊆ A ∪ B)
                [ lapply H4 #H6 @ax_inclusion2 #y #H7 cut (y ∈ A)
                  [ cut (∀y. y ∈ X → y ∈ A)
                    [ @ax_inclusion1 @H6
                    | #H8 lapply H7 @H8
                    ]
                  | #H8 cut (y ∈ A ∨ y ∈ B)
                    [ @or_introl //
                    | @ax_union2
                    ]
                  ]
                | //
                ]
              ]
            | #H4 @H4
            ]
          | #H4 /3/
          ]
        ]
      | #H2  cut (z ⊆ A ∪ B)
        [ cut (z ⊆ B)
          [  @ax_powerset1 @H2
          | #H3 @ax_inclusion2 #y #H4 cut (y ∈ B)
            [ /3/
            | #H5 cut (y ∈ A ∨ y ∈ B)
              [ @or_intror //
              | @ax_union2
              ]
            ]
          ]
        | #H4 @ax_powerset2 @H4
        ]
      ]
    ]
  | #H @ax_inclusion2 @H
  ]
qed.

(* Exercise 16 *)
(* Nel corso della dimostrazione può essere utile tornare indietro e dimostrare 
separatamente una qualche proprietà sull'inclusione e l'intersezione *)
lemma in_inclusion: ∀ A, B. ∀x. (x ∈ A) → (A ⊆ B) → x ∈ B.
#A #B #x
#H1 #H2 cut (∀x. x ∈ A → x ∈ B)
  [ @ax_inclusion1 @H2
  | #H3 lapply H1 @H3
  ].
qed.

theorem intersection_powerset: ∀A, B. (powerset A) ∩ (powerset B) = powerset (A ∩ B).
#A #B
cut (∀z. z ∈ (powerset A) ∩ (powerset B) ↔ z ∈ powerset (A ∩ B) )
 [ #z normalize %1
   [ #H @ax_powerset2 cut (z ⊆ A ∧ z ⊆ B)
     [ %1
       [ cut (z ∈ powerset A ∧ z ∈ powerset B)
         [ lapply H @ax_intersect1 
         | #H1 elim H1 #H2 #H3 @ax_powerset1 @H2
         ]
       | cut (z ∈ powerset A ∧ z ∈ powerset B)
         [ lapply H @ax_intersect1
         | #H1 elim H1 #H2 #H3 @ax_powerset1 @H3
         ]
       ]
     | #H1 cut (∀x. x ∈ z → x ∈ A ∧ x ∈ B )
       [ #x #H2 elim H1 #H3 #H4 %
         [ lapply H3 lapply H2 @in_inclusion
         | lapply H4 lapply H2 @in_inclusion
         ]
       | #H2 cut (∀x. x ∈ z → x ∈ A ∩ B)
         [ #x #H3 cut (x ∈ A ∧ x ∈ B)
           [ lapply H3 @H2
           | @ax_intersect2
           ]
         | #H3 @ax_inclusion2 @H3
         ]
       ]
     ]
   | #H @ax_intersect2 %
     [ @ax_powerset2 cut (∀x. x ∈ z → x ∈ A)
       [ #x #H1 cut (z ⊆ A ∩ B)
         [ @ax_powerset1 @H
         | #H2 cut (x ∈ A ∩ B)
           [ lapply H2 lapply H1 @in_inclusion
           | #H3 cut (x ∈ A ∧ x ∈ B)
             [ lapply H3 @ax_intersect1
             | #H4 elim H4 //
             ]
           ]
         ]
       | #H1 @ax_inclusion2 @H1
       ]
     | @ax_powerset2 cut (∀x. x ∈ z → x ∈ B)
       [ #x #H1 cut (z ⊆ A ∩ B)
         [ @ax_powerset1 @H
         | #H2 cut (x ∈ A ∩ B)
           [ lapply H2 lapply H1 @in_inclusion
           | #H3 cut (x ∈ A ∧ x ∈ B)
             [ lapply H3 @ax_intersect1
             | #H4 elim H4 //
             ]
           ]
         ]
       | #H1 @ax_inclusion2 @H1
       ]
     ]
   ]
 | @ax_extensionality
 ]
qed. 
            
 
 


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

axiom ax_empty: ∀X. (X ∈ ∅) → False.

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
  assume A: set
  assume B: set
  we need to prove (∀Z. Z ∈ A → Z ∈ A ∪ B) (I)
    assume Z: set
    suppose (Z ∈ A) (ZA)
    we need to prove (Z ∈ A ∨ Z ∈ B) (I1)
      by ZA,or_introl
    done
  by I1,ax_union2 done
  by I, ax_inclusion2 done
qed.

(* Exercise 2 *)
theorem union_idempotent: ∀A. A ∪ A = A.
 assume A: set
 we need to prove (∀Z. Z ∈ A ∪ A ⇔ Z ∈ A) (II)
  assume Z: set
  we need to prove (Z ∈ A ∪ A → Z ∈ A) (I1)
   suppose (Z ∈ A ∪ A) (Zu)
   by ax_union1, Zu we proved (Z ∈ A ∨ Z ∈ A) (Zor)
   we proceed by cases on Zor to prove (Z ∈ A)
    case or_introl
     suppose (Z ∈ A) (H)
     by H
    done
    case or_intror
     suppose (Z ∈ A) (H)
     by H
  done
  we need to prove (Z ∈ A → Z ∈ A ∪ A) (I2)
   suppose (Z ∈ A) (ZA)
   by ZA, or_introl we proved (Z ∈ A ∨ Z ∈ A) (Zor)
   by Zor, ax_union2 
  done
  by I1,I2,conj
 done
 by ax_extensionality, II
done
qed.

(* Exercise 3 *)
theorem intersection_idempotent: ∀A. A ∩ A = A.
 assume A: set
 we need to prove (∀Z. Z ∈ A ∩ A ⇔ Z ∈ A) (II)
  assume Z: set
  we need to prove (Z ∈ A ∩ A → Z ∈ A) (I1)
   suppose (Z ∈ A ∩ A) (Zi)
   by ax_intersect1, Zi we have (Z ∈ A) (ZA1) and (Z ∈ A) (ZA2)
   by ZA1
  done
  we need to prove (Z ∈ A → Z ∈ A ∩ A) (I2)
   suppose (Z ∈ A) (ZA)
   by ZA, conj we proved (Z ∈ A ∧ Z ∈ A) (Zand)
   by Zand, ax_intersect2
  done
  by I1,I2,conj
 done
 by ax_extensionality, II
done
qed.

(* Exercize 4 *)
theorem empty_absurd: ∀X, A. X ∈ ∅ → X ∈ A.
 assume X: set. 
 assume A: set
 suppose (X ∈ ∅) (XE)
 by XE, ax_empty we proved False (bottom)
 using (ABSURDUM bottom) 
done
qed.
  
(* Exercise 5 *)
theorem intersect_empty: ∀A. A ∩ ∅ = ∅.
 assume A: set
 we need to prove (∀Z. Z ∈ A ∩ ∅ ⇔ Z ∈ ∅) (II)
   assume Z: set
   we need to prove (Z ∈ A ∩ ∅ → Z ∈ ∅) (I1)
     suppose (Z ∈ A ∩ ∅) (Ze)
     we need to prove (Z ∈ ∅)
     by Ze,ax_intersect1 we have (Z ∈ A) (ZA) and (Z ∈ ∅) (ZE)
     by ZE
   done
   we need to prove (Z ∈ ∅ → Z ∈ A ∩ ∅) (I2)
     suppose (Z ∈ ∅) (ZE)
     by ZE, ax_empty we proved False (bottom)
     using (ABSURDUM bottom) done
   by I1,I2,conj
 done
 by (ax_extensionality),(II)
done
qed.

(* Exercise 6 *)
theorem union_empty: ∀A. A ∪ ∅ = A.
 assume A: set
 we need to prove (∀Z. Z ∈ A ∪ ∅ ⇔ Z ∈ A) (II)
   assume Z: set
   we need to prove (Z ∈ A → Z ∈ A ∪ ∅) (I1)
     suppose (Z ∈ A) (ZA)
     by (ZA),or_introl we proved (Z ∈ A ∨ Z ∈ ∅) (Zor)
     by ax_union2,Zor
   done
   we need to prove (Z ∈ A ∪ ∅ → Z ∈ A) (I2)
     suppose (Z ∈ A ∪ ∅) (Zu)
     by Zu, (ax_union1) we proved (Z ∈ A ∨ Z ∈ ∅) (Zor)
     we proceed by cases on (Zor) to prove (Z ∈ A)
      case or_introl
       suppose (Z ∈ A) (H)
       by H 
      done
      case or_intror
       suppose (Z ∈ ∅) (H)
       by H, ax_empty we proved False (bottom)
       using (ABSURDUM bottom) 
      done
    by I1, I2, conj
  done
  by ax_extensionality,II
 done
qed.

(* Exercise 7 *)
theorem intersect_commutative: ∀A,B. A ∩ B = B ∩ A.
 assume A: set
 assume B: set
 we need to prove (∀Z. Z ∈ A ∩ B ⇔ Z ∈ B ∩ A) (II)
   assume Z: set
   we need to prove (Z ∈ A ∩ B → Z ∈ B ∩ A) (I1)
     suppose (Z ∈ A ∩ B) (ZAB)
     we need to prove (Z ∈ B ∩ A)
      by ax_intersect1,ZAB we have (Z ∈ A) (ZA) and (Z ∈ B) (ZB)
      by ax_intersect2,conj,ZB,ZA
   done
   we need to prove (Z ∈ B ∩ A → Z ∈ A ∩ B) (I2)
     suppose (Z ∈ B ∩ A) (ZBA)
     we need to prove (Z ∈ A ∩ B)
     by ax_intersect1,ZBA we have (Z ∈ B) (ZB) and (Z ∈ A) (ZA)
     by ax_intersect2,conj,ZA,ZB
   done
   by conj,I1,I2
 done
 by ax_extensionality,II
done
qed.

(* Exercise 8 *)
theorem union_commutative: ∀A,B. A ∪ B = B ∪ A.
 assume A: set
 assume B: set
 we need to prove (∀Z. Z ∈ A ∪ B ⇔ Z ∈ B ∪ A) (II)
   assume Z: set
   we need to prove (Z ∈ A ∪ B → Z ∈ B ∪ A) (I1)
     suppose (Z ∈ A ∪ B) (ZAB)
     we need to prove (Z ∈ B ∪ A)
     we need to prove (Z ∈ B ∨ Z ∈ A) (I)
       by ax_union1,ZAB we proved (Z ∈ A ∨ Z ∈ B) (Zor)
       we proceed by cases on Zor to prove (Z ∈ B ∨ Z ∈ A)
         case or_introl
           suppose (Z ∈ A) (H)
           by H,or_intror
         done
         case or_intror
            suppose (Z ∈ B) (H)
            by H,or_introl
         done
     by ax_union2,I
   done
   we need to prove (Z ∈ B ∪ A → Z ∈ A ∪ B) (I2)
     suppose (Z ∈ B ∪ A) (ZBA)
     we need to prove (Z ∈ A ∪ B)
     we need to prove (Z ∈ A ∨ Z ∈ B) (I)
       by ax_union1,ZBA we proved (Z ∈ B ∨ Z ∈ A) (Zor)
       we proceed by cases on Zor to prove (Z ∈ A ∨ Z ∈ B)
         case or_introl
           suppose (Z ∈ B) (H)
           by H,or_intror
         done
         case or_intror
           suppose (Z ∈ A) (H)
           by H,or_introl
         done
     by ax_union2,I
   done
   by conj,I1,I2
 done.        
 by ax_extensionality,II
done
qed.

(* Exercise 9 *)
theorem distributivity1: ∀A,B,C. A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C).
 assume A: set
 assume B: set
 assume C: set
 we need to prove (∀Z. Z ∈ A ∪ (B ∩ C) ⇔ Z ∈ (A ∪ B) ∩ (A ∪ C)) (II)
  assume Z:set
  we need to prove (Z ∈ (A ∪ B) ∩ (A ∪ C) → Z ∈ A ∪ (B ∩ C)) (I1)
   suppose (Z ∈ (A ∪ B) ∩ (A ∪ C)) (Zint)
   by Zint, ax_intersect1 we have (Z ∈ (A ∪ B)) (Zu1) and (Z ∈ (A ∪ C)) (Zu2)
   by Zu1, ax_union1 we proved (Z ∈ A ∨ Z ∈ B) (Zor1)
   by Zu2, ax_union1 we proved (Z ∈ A ∨ Z ∈ C) (Zor2)
   we proceed by cases on Zor1 to prove (Z ∈ A ∪ B ∩ C)
   case or_introl
    suppose (Z ∈ A) (H)
    by or_introl,H,ax_union2 
    done
   case or_intror
    suppose (Z ∈ B) (H)
    we proceed by cases on Zor2 to prove (Z ∈ A ∪ B ∩ C)
    case or_introl
     suppose (Z ∈ A) (H1)
     by or_introl,H1,ax_union2 
    done
    case or_intror
     suppose (Z ∈ C) (H1)
     by H,H1,conj,ax_intersect2 we proved (Z ∈ B ∩ C) (K1)
     by K1,or_intror,ax_union2 
  done
  we need to prove (∀Z. Z ∈ A ∪ (B ∩ C) → Z ∈ (A ∪ B) ∩ (A ∪ C)) (I2)
   assume Z: set
   suppose (Z ∈ A ∪ (B ∩ C)) (Zu)
   by Zu,ax_union1 we proved (Z ∈ A ∨ Z ∈ B ∩ C) (Zor)
   we proceed by cases on Zor to prove (Z∈(A∪B)∩(A∪C))
   case or_introl
    suppose (Z ∈ A) (H)
    by H,or_introl,ax_union2 we proved (Z∈(A∪B)) (K1)
    by H,or_introl,ax_union2 we proved (Z∈(A∪C)) (K2)
    by K1,K2,conj,ax_intersect2 
   done
   case or_intror
    suppose (Z ∈ B ∩ C) (H)
    by ax_intersect1,H  we have (Z ∈ B) (H1) and (Z ∈ C) (H2)
    by H1,or_intror,ax_union2 we proved (Z∈(A∪B)) (K1)
    by H2,or_intror,ax_union2 we proved (Z∈(A∪C)) (K2)
    by K1,K2,conj,ax_intersect2
  done
  by I1,I2,conj 
 done
 by II, ax_extensionality 
done
qed.

(* Exercise 10 *)
theorem distributivity2: ∀A,B,C. A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C).
 assume A: set
 assume B: set
 assume C: set
 we need to prove (∀Z. Z ∈ A ∩ (B ∪ C) ⇔ Z ∈ (A ∩ B) ∪ (A ∩ C)) (II)
  assume Z:set
  we need to prove (Z ∈ A ∩ (B ∪ C) → Z ∈ (A ∩ B) ∪ (A ∩ C)) (I1)
   suppose (Z ∈ A ∩ (B ∪ C)) (K1)
   by ax_intersect1, K1 we have (Z ∈ A) (K1A) and (Z ∈ B ∪ C) (K1BC)
   by ax_union1, K1BC we proved (Z ∈ B ∨ Z ∈ C) (Zor)
   we proceed by cases on (Zor) to prove (Z ∈ (A ∩ B) ∪ (A ∩ C))
   case or_introl
    suppose (Z ∈ B) (H)
    by H,K1A,ax_intersect2,conj we proved (Z ∈ A ∩ B) (H1)
    by H1,or_introl,ax_union2 
   done
   case or_intror
    suppose (Z ∈ C) (H)
    by H,K1A,ax_intersect2,conj we proved (Z ∈ A ∩ C) (H1)
    by H1,or_intror,ax_union2 
  done
  we need to prove (Z ∈ (A ∩ B) ∪ (A ∩ C) → Z ∈ A ∩ (B ∪ C)) (I2)
   suppose (Z ∈ (A ∩ B) ∪ (A ∩ C)) (K2)
   by ax_union1,K2 we proved (Z ∈ (A ∩ B) ∨ Z ∈ (A ∩ C)) (Zor)
   we proceed by cases on Zor to prove (Z ∈ A ∩ (B ∪ C))
   case or_introl
    suppose (Z ∈ A∩B) (H)
    by H,ax_intersect1 we have (Z ∈ A) (ZA) and (Z ∈ B) (ZB)
    by ZB,or_introl,ax_union2 we proved (Z ∈ B ∪ C) (ZBC)
    by ZA, ZBC, ax_intersect2, conj
   done
   case or_intror
    suppose (Z ∈ A∩C) (H)
    by H,ax_intersect1 we have (Z ∈ A) (ZA) and (Z ∈ C) (ZC)
    by ZC,or_intror,ax_union2 we proved (Z ∈ B ∪ C) (ZBC)
    by ZA, ZBC, ax_intersect2, conj
  done
  by I1,I2,conj
 done
 by II,ax_extensionality
done
qed.


(********** Inizio degli esercizi del laboratorio 2 *******************)

(* Exercise 11 *)
theorem antisymmetry_inclusion: ∀A,B. A ⊆ B → B ⊆ A → A = B.
 assume A: set
 assume …
 suppose (A ⊆ B) (AB)
 suppose …
 we need to prove (∀Z. Z ∈ A ⇔ Z ∈ B) (P)
  assume … 
  by AB, ax_inclusion1 we proved … (AB')
  by … we proved (Z ∈ B → Z ∈ A) (BA')
  by …
 done
 by … 
done
qed.

(* Exercise 12 *)
theorem reflexivity_inclusion: ∀A. A ⊆ A.
 assume …
 we need to prove (∀Z. Z ∈ A → Z ∈ A) (ZAtoZA)
  assume …
  suppose …
  by … 
 done
 by … 
done
…

(* Exercise 13 *)
theorem transitivity_inclusion: ∀A,B,C. A ⊆ B → B ⊆ C → A ⊆ C.
 assume …
 assume …
 …
 suppose …
 …
 we need to prove …
  …
  …
  by … we proved …
  by … 
 done
 by …
done
…



(************ POWERSET ***************)
axiom powerset: set → set.

axiom ax_powerset1: ∀A. ∀Z. (Z ∈ powerset A → Z ⊆ A).
axiom ax_powerset2: ∀A. ∀Z. (Z ⊆ A → Z ∈ powerset A).

(* Exercise 14 *)
theorem powerset_emptyset: ∀A. A ∈ powerset ∅ → A = ∅.
 assume …
 suppose … (AE)
 by ax_powerset1, … we proved … (sub)
 we need to prove (∅ ⊆ A) (sub')
  we need to prove … (EA)
   assume …
   by empty_absurd
  done
  by …, EA
 done
 by antisymmetry_inclusion, … 
done
qed.

(* Exercise 15 *)
theorem union_powerset: ∀A, B. (powerset A) ∪ (powerset B) ⊆ powerset (A ∪ B).
 …
 …
 we need to prove …
  …
  …
  by … we proved … (PAorPB)
  we proceed by cases on … to prove (Z ∈ powerset (A ∪ B))
  case or_introl
   suppose (Z ∈ powerset A) (H)
   by … we proved …
   by union_inclusion we proved …
   by … we proved (Z ⊆ A ∪ B) (ZAB)
   by … 
  done
  case or_intror
   suppose (Z ∈ powerset B) (H)
   …
   …
   …
   by … we proved (Z ⊆ A ∪ B) (ZAB)
   by … 
 done
 by … 
done
…

…

(* Exercise 16 *)
(* Nel corso della dimostrazione può essere utile tornare indietro e dimostrare 
separatamente una qualche proprietà sull'inclusione e l'intersezione *)
theorem intersection_powerset: ∀A, B. (powerset A) ∩ (powerset B) = powerset (A ∩ B).
 …
  
 
 

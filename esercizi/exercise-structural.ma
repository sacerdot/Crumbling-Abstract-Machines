(**************************************************************************)
(*       ___	                                                          *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||       A.Asperti, C.Sacerdoti Coen,                          *)
(*      ||A||       E.Tassi, S.Zacchiroli                                 *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU Lesser General Public License Version 2.1         *)
(*                                                                        *)
(**************************************************************************)

(* Esercizio 0 
   ===========
   
   Compilare i seguenti campi:
   
   Nome1: ...
   Cognome1: ...
   Matricola1: ...
   Account1: ...
   
   Nome2: ...
   Cognome2: ...
   Matricola2: ...
   Account2: ...

   Nota: salvate spesso per evitare la perdita del lavoro svolto in caso di
   crash dell'applicazione.

*)



(* ATTENZIONE
   ==========
   
   Non modificare la seguente riga che carica la definizione di uguaglianza.
*)
include "basics/logic.ma".


(* Esercizio 1 
   ===========
   
   Definire il seguente linguaggio (o tipo) di espressioni riempiendo gli spazi.
   
   Expr :: "Zero" | "One" | "Minus" Expr | "Plus" Expr Expr | "Mult" Expr Expr 
*)
inductive Expr : Type[0] ≝
| Zero: Expr
| One: Expr
| Minus: Expr → Expr
| Plus: Expr → Expr → Expr
| Mult: Expr → Expr → Expr
.

(* La prossima linea è un test per verificare se la definizione data sia
   probabilmente corretta. Essa definisce `test_Expr` come un'abbreviazione
   dell'espressione `Mult Zero (Plus (Minus One) Zero)`, verificando inoltre
   che l'espressione soddisfi i vincoli di tipo dichiarati sopra. Eseguitela. *)

definition test_Expr : Expr ≝ Mult Zero (Plus (Minus One) Zero).

(* Come esercizio, provate a definire espressioni che siano scorrette rispetto
   alla grammatica/sistema di tipi. Per esempio, scommentate la seguenti
   righe e osservate i messaggi di errore:
   
definition bad_Expr1 : Expr ≝ Mult Zero.
definition bad_Expr2 : Expr ≝ Mult Zero Zero Zero.
definition bad_Expr3 : Expr ≝ Mult Zero Plus.
*)

(* Esercizio 2 
   ===========
   
   Definire il linguaggio (o tipo) dei numeri naturali.

   nat ::= "O" | "S" nat   
*)

inductive nat : Type[0] ≝
| O: nat
| S: nat → nat
.

definition one : nat ≝ S O.
definition two : nat ≝ S (S O).
definition three : nat ≝ S (S (S O)).

(* Esercizio 3
   ===========
   
   Definire il linguaggio (o tipo) delle liste di numeri naturali.
   
   list_nat ::= "Nil" | "Snoc" nat list_nat
   
   dove Nil sta per lista vuota e Snoc aggiunge in testa un numero naturale a
   una lista di numeri naturali.
   
   Per esempio, `Snoc O (Snoc (S O) (Snoc (S (S O)) Nil))` rappresenta la lista
   `[1,2,3]`.
*)

inductive list_nat : Type[0] ≝
| Nil: list_nat
| Snoc: nat → list_nat → list_nat
.

(* La seguente lista contiene 1,2,3 *)
definition one_two_three : list_nat ≝ Snoc one (Snoc two (Snoc three Nil)).

(* Completate la seguente definizione di una lista contenente due uni. *)

definition one_one : list_nat ≝ Snoc (S O) (Snoc (S O) Nil).

(* Esercizio 4
   ===========
   
   Definire il linguaggio degli alberi binari (= dove ogni nodo che non è una
   foglia ha esattamente due figli) le cui foglie siano numeri naturali.
   
   tree_nat ::= "Leaf" nat | "Node" tree_nat tree_nat
*)

inductive tree_nat : Type[0] ≝
| Leaf: nat → tree_nat
| Node: tree_nat → tree_nat → tree_nat
. 

(* Il seguente albero binario ha due foglie, entrambe contenenti uni. *)
definition one_one_tree : tree_nat ≝ Node (Leaf one) (Leaf one).

(* Definite l'albero       /\
                          0 /\
                           1  2  *)
definition zero_one_two_tree : tree_nat ≝ Node (Leaf O) (Node (Leaf (S O)) (Leaf (S (S O)))).

(* Esercizio 5
   ===========
   
   Osservare come viene definita la somma di due numeri in Matita per
   ricorsione strutturale sul primo.
   
   plus O m = m
   plus (S x) m = S (plus x m) *)

let rec plus n m on n ≝
 match n with
 [ O ⇒ m
 | S x ⇒ S (plus x m) ].

(* Provate a introdurre degli errori nella ricorsione strutturale. Per esempio,
   omettete uno dei casi o fate chiamate ricorsive non strutturali e osservate
   i messaggi di errore di Matita. *)

(* Per testare la definizione, possiamo dimostrare alcuni semplici teoremi la
   cui prova consiste semplicemente nell'effettuare i calcoli. *)
theorem test_plus: plus one two = three.
normalize // qed.

(* Esercizio 6
   ===========

   Completare la seguente definizione, per ricorsione strutturale, della
   funzione `size_E` che calcola la dimensione di un'espressione in numero
   di simboli.
   
   size_E Zero = 1
   size_E One = 1
   size_E (Minus E) = 1 + size_E E
   ... 
*)
let rec size_E E on E ≝
 match E with
  [ Zero ⇒ one 
  | One ⇒ one
  | Minus E ⇒ plus one (size_E E)
  | Plus E1 E2 ⇒ plus one (plus (size_E E1) (size_E E2))
  | Mult E1 E2 ⇒ plus one (plus (size_E E1) (size_E E2))
  ]
.

theorem test_size_E : size_E test_Expr = plus three three.
normalize // qed.

(* Esercizio 7
   ===========
   
   Definire in Matita la funzione `sum` che, data una `list_nat`, calcoli la
   somma di tutti i numeri contenuti nella lista. Per esempio,
   `sum one_two_three` deve calcolare sei.
*)

let rec sum l on l ≝
 match l with
  [ Nil ⇒ O
  | Snoc l1 l2 ⇒ plus l1 (sum l2)
  ]
 .

theorem test_sum : sum one_two_three = plus three three.
normalize // qed.

(* Esercizio 8
   ===========
   
   Definire la funzione `rightmost` che, dato un `tree_nat`, restituisca il
   naturale contenuto nella foglia più a destra nell'albero. *)

let rec rightmost n on n ≝
 match n with
  [ Leaf n ⇒ n
  | Node n1 n2 ⇒ rightmost n2
  ]
 .

theorem test_rightmost : rightmost zero_one_two_tree = two.
normalize // qed.

(* Esercizio 9
   ===========
   
   Definire la funzione binaria `append` che, date due `list_nat` restituisca la
   `list_nat` ottenuta scrivendo in ordine prima i numeri della prima lista in
   input e poi quelli della seconda.
   
   Per esempio, `append (Snoc one (Snoc two Nil)) (Snoc 0 Nil)` deve restituire
   `Snoc one (Snoc two (Snoc 0 nil))`. *)
let rec append l1 l2 on l1 ≝ 
 match l1 with
  [ Nil ⇒ l2
  | Snoc l m ⇒ Snoc l (append m l2)
  ]
 .  

theorem test_append : append (Snoc one Nil) (Snoc two (Snoc three Nil)) = one_two_three.
normalize // qed.

(* Esercizio 10
   ============
   
   Definire la funzione `visit` che, dato un `tree_nat`, calcoli la `list_nat`
   che contiene tutti i numeri presenti nelle foglie dell'albero in input,
   nell'ordine in cui compaiono nell'albero da sinistra a destra.
   
   Suggerimento: per definire tree_nat usare la funzione `append` già definita
   in precedenza.

   Esempio: `visit zero_one_two_tree = Snoc O (Snoc one (Snoc two Nil))`.    
*)
let rec visit n on n ≝
 match n with
  [ Leaf n ⇒ Snoc n Nil
  | Node n1 n2 ⇒ append (visit n1) (visit n2)
  ]
 .

theorem test_visit : visit zero_one_two_tree = Snoc O (Snoc one (Snoc two Nil)).
normalize // qed.

let rec size_l l on l ≝
 match l with 
  [ Nil ⇒ O
  | Snoc n l1 ⇒ S (size_l l1)
  ]
  .

let rec size_t n on n ≝
 match n with
  [ Leaf m ⇒ S O
  | Node l m ⇒ plus (size_t l) (size_t m)
  ]
 .

let rec sum_l l on l ≝
 match l with 
  [ Nil ⇒ O
  | Snoc n l1 ⇒ plus n (sum_l l1)
  ]
  .

let rec sum_t n on n ≝
 match n with
  [ Leaf m ⇒ m
  | Node l m ⇒ plus (sum_t l) (sum_t m)
  ]
 .
 
lemma list_len: ∀l, m. plus (size_l l) (size_l m)= size_l (append l m).
#l #m elim l
 [ normalize //
 | #x #n #Hind normalize >Hind //
 ]
qed.

lemma plus_assoc: ∀m, n, o. plus m (plus  n o)= plus (plus m n) o.
#m #n #o elim m
[ //
| #x #Hind normalize >Hind //
] qed.

lemma pluz_zero: ∀m. m= plus m O.
#m elim m
 [ //
 | #x #Hind normalize //
 ]
qed.

lemma list_sum: ∀l, m. plus (sum_l l) (sum_l m)= sum_l (append l m).
#l #m elim l
 [ normalize //
 | #x #n #Hind normalize cut (plus (plus x (sum_l n)) (sum_l m)=plus x (plus (sum_l n) (sum_l m)))
  [ //
  | #H >H >Hind //
 ]
qed.

theorem tree_visit_size: ∀t: tree_nat. size_t t = size_l (visit t).
#t elim t
 [ #X normalize //
 | #tt #ttt #H1 #H2 normalize >H1 >H2 normalize @list_len
 ].
qed.

theorem sum_visit_tree: ∀t: tree_nat. sum_t t = sum_l (visit t).
#t elim t
 [ #x normalize //
 | #tt #ttt #Hind #Hindd normalize >Hind >Hindd //
 ]
qed.



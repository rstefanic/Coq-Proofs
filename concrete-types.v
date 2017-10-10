Module Boolean.

Inductive bool := 
  | true
  | false.

(*** Bool Functions ***)
Definition negate : bool -> bool :=
  fun (b:bool) =>
  match b with
     true => false
   | false => true
end.

Definition and (b b' : bool) : bool :=
  match b with
  | true => b'
  | false => false
end.

Definition or (b b' : bool) : bool :=
  match b with
  | false => b'
  | true => true
end.

Definition nand (b b' : bool) : bool :=
  match b with
  | false => true
  | true => match b' with
            | false => true
            | true => false
            end
end.

Definition nor (b b' : bool) : bool :=
  match b with
  | true => false
  | false => match b' with
             | true => false
             | false => true
             end
end.

(*** Bool Notation ***)
Notation "x && y" := (and x y).
Notation "x || y" := (or x y).


(*** Bool Proofs ***)

(* && Proofs *)
Example test_and_tt : true && true = true.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_and_tf : true && false = false.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_and_ft : false && true = false.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_and_ff : false && false = false.
Proof.
  simpl.
  reflexivity.
Qed.

(* || Proofs *)
Example test_or_tt : true || true = true.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_or_tf : true || false = true.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_or_ft : false || true = true.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_or_ff : false || false = false.
Proof.
  simpl.
  reflexivity.
Qed.


(* NAND Proofs *)
Example test_nand_tt : (nand true true) = false.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_nand_tf : (nand true false) = true.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_nand_ft : (nand false true) = true.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_nand_ff : (nand false false) = true.
Proof.
  simpl.
  reflexivity.
Qed.

(* NOR Proofs *)
Example test_nor_tt : (nor true true) = false.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_nor_tf : (nor true false) = false.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_nor_ft : (nor false true) = false.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_nor_ff : (nor false false) = true.
Proof.
  simpl.
  reflexivity.
Qed.

End Boolean.


Inductive byte := 
  Byte(b7 b6 b5 b4 b3 b2 b1 b0 : bool).

Definition negate_byte : byte -> byte :=
  fun (b : byte) =>
  match b with
    Byte b7 b6 b5 b4 b3 b2 b1 b0 =>
    Byte (negate b7) (negate b6) (negate b5) (negate b4)
         (negate b3) (negate b2) (negate b1) (negate b0)
end.

Compute negate_byte (Byte true true true true false false false false).

Inductive string := 
  | EmptyString
  | NonEmptyString (head : byte) (tail : string).

Definition h : byte := Byte false true true false true false false false.
Definition i : byte := Byte false true true false true false false true.

Definition concat : string -> (string -> string) :=
  (* Must add a fixpoint operator to recursively call concat/f *)
  fix f(s1 : string) {struct s1}: string -> string :=
  fun (s2 : string) =>
  match s1 with
    EmptyString => s2
  | NonEmptyString b s => NonEmptyString b ((f s) s2)
end.

Inductive list (A : Type) := 
    nil
  | cons (head : A) (tail : list A).

Definition hi_as_a_list : list byte :=
  cons byte h (cons byte i (nil byte)).

(*Fixpoint append (A : Type) (ls1 ls2 : list A) {struct ls1} : list A :=*)

Definition append (A : Type) : list A -> list A -> list A :=
fix f (ls1: list A) {struct ls1} : list A -> list A :=
fun (ls2: list A) => 
  match ls1 with
    nil _ => ls2
  | cons _ h t => cons A h ((f t) ls2)
end.

Definition hi : string := NonEmptyString (h : byte) (NonEmptyString (i : byte) (EmptyString)).

Compute concat (NonEmptyString h EmptyString) (NonEmptyString i EmptyString).

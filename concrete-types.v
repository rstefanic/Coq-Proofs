Inductive bool := 
  | true
  | false.

Definition negate : bool -> bool :=
  fun (b:bool) =>
  match b with
     true => false
   | false => true
end.

Compute negate true.

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

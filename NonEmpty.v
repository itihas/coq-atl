Require Import List.

Inductive nonempty (A:Type) : Type := mknonempty: A -> (list A) -> nonempty A.

Notation "a ::: la" := (mknonempty _ a la) (at level 61).

Definition ne : nonempty nat := 1 ::: nil.

Definition nonempty_last {A:Type} (n:nonempty A) :=
  match n with
  | mknonempty _ a b => last b a
  end.

Definition nonempty_cons {A:Type} (a:A) (n:nonempty A) :=
  match n with
  | mknonempty _ b c => a:::b::c
  end.

Definition nonempty_head {A:Type} (n:nonempty A) :=
  match n with
  | mknonempty _ a b => a
  end.

Definition nonempty_nth {A:Type} (i:nat) (n:nonempty A) (d:A) :=
  match i with
  | 0 => match n with
         | mknonempty _ a b => a
         end
  | S i' => match n with
           | mknonempty _ a b => nth i' b d
           end
  end.

Definition nonempty_length {A:Type} (n:nonempty A) :=
  match n with
  | mknonempty _ a b => S (length b)
  end.
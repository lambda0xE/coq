Require Import List.
Import ListNotations.
Require Import PeanoNat.

Inductive vector : Type :=
  | Nil : vector
  | Cons : nat -> vector -> vector.

Fixpoint add_vectors (v1 v2 : vector) : vector :=
  match (v1, v2) with
  | (Nil, Nil) => Nil
  | (Cons hd1 tl1, Cons hd2 tl2) => Cons (hd1 + hd2) (add_vectors tl1 tl2)
  | _ => Nil 
  end.

Fixpoint vector_to_list (v : vector) : list nat :=
  match v with
  | Nil => []
  | Cons hd tl => hd :: (vector_to_list tl)
  end.

Fixpoint list_to_vector (l : list nat) : vector :=
  match l with
  | [] => Nil
  | hd :: tl => Cons hd (list_to_vector tl)
  end.

Lemma add_vectors_correct :
  forall v1 v2 : vector,
    length (vector_to_list v1) = length (vector_to_list v2) ->
    vector_to_list (add_vectors v1 v2) =
    map (fun p => fst p + snd p) (combine (vector_to_list v1) (vector_to_list v2)).
Proof.
  intros v1 v2 Hlen.
  revert v2 Hlen.
  induction v1 as [| hd1 tl1 IH1].
  - intros v2 Hlen. destruct v2; try discriminate Hlen. reflexivity.
  - intros v2 Hlen. destruct v2 as [| hd2 tl2]; try discriminate Hlen.
    simpl. rewrite (IH1 tl2).
    + simpl. rewrite Nat.add_comm. reflexivity.
    + simpl in Hlen. injection Hlen as Hlen'. apply Hlen'.
Qed.

Fixpoint vector_length (v : vector) : nat :=
  match v with
  | Nil => 0
  | Cons _ tl => S (vector_length tl)
  end.

Fixpoint zero_vector (n : nat) : vector :=
  match n with
  | 0 => Nil
  | S m => Cons 0 (zero_vector m)
  end.

Example vector_length_example :
  let v := Cons 1 (Cons 2 (Cons 3 Nil)) in
  vector_length v = 3.
Proof.
  reflexivity.
Qed.

Example zero_vector_example :
  let n := 4 in
  let zero := zero_vector n in
  vector_to_list zero = [0; 0; 0; 0].
Proof.
  reflexivity.
Qed.

Print add_vectors_correct.
Print vector_length_example.
Print zero_vector_example.

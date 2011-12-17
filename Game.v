Inductive player := L | R.

Definition opponent pl :=
  match pl with
    | L => R
    | R => L
  end.

Inductive game: Set :=
| empty: game
| addMove: player -> game -> game (* original *) -> game
.

Inductive winningStrategy: game -> player -> Set :=
| take: forall p m o, losingFate m (opponent p) -> winningStrategy (addMove p m o) p 
| pass: forall p m o q, winningStrategy o p -> winningStrategy (addMove q m o) p
with losingFate: game -> player -> Set :=
| stuck: forall p, losingFate empty p
| whichever: forall m p o, winningStrategy m (opponent p) -> losingFate o p ->
  losingFate (addMove p m o) p
| wait: forall p q o m, losingFate o p -> q = opponent p -> losingFate (addMove q m o) p
.

Definition decision (g: game) (p: player):
  winningStrategy g p + losingFate g p.
Proof with auto.
generalize p.
clear p.
induction g.
  intro p.
  right.
  apply stuck.

  rename p into mover.
  intro p.
  destruct IHg1 with (opponent p); destruct IHg2 with p; clear IHg1 IHg2; destruct mover; destruct p; simpl in *.

  
  left.
  apply pass...

  left.
  apply pass...

  left.
  apply pass...

  left.
  apply pass...

  right.
  apply whichever...

  right.
  apply wait...

  right.
  apply wait...

  right.
  apply whichever...

  left.
  apply pass...

  left.
  apply pass...

  left.
  apply pass...

  left.
  apply pass...

  left.
  apply take...

  right.
  apply wait...

  right.
  apply wait...

  left.
  apply take...
Defined.

(* next: never winning and losing at the same time *)

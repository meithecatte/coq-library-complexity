From Undecidability.L.Datatypes Require Export LSum.
From Complexity.L Require Export ComputableTime.

(* ** Encoding of sum type *)
Section Fix_XY.

  Variable X Y:Type.
  
  Variable intX : encodable X.
  Variable intY : encodable Y.

  Global Instance termT_inl : computableTime' (@inl X Y) (fun _ _ => (1,tt)).
  Proof.
    extract constructor.
    solverec.
  Qed.

   Global Instance termT_inr : computableTime' (@inr X Y) (fun _ _ => (1,tt)).
  Proof.
    extract constructor.
    solverec.
  Qed.
End Fix_XY.

Lemma size_sum X Y `{encodable X} `{encodable Y} (l: X + Y):
  size (enc l) = match l with inl x => size (enc x) + 5 | inr x => size (enc x) + 4 end.
Proof.
  unfold enc at 1.
  destruct l as [x|x]. all:cbn.
  all:lia. 
Qed.

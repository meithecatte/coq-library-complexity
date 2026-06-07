From Undecidability.L.Datatypes Require Export LOptions.
From Complexity.L Require Import ComputableTime.
Import L_Notations.

(* ** Encoding of option type *)
Section Fix_X.
  Variable X:Type.
  Context {intX : encodable X}.

  Global Instance termT_Some : computableTime' (@Some X) (fun _ _ => (1,tt)).
  Proof.
    extract constructor. solverec.
  Defined. (*because next lemma*)

  Lemma oenc_correct_some (s: option X) (v : term) : lambda v -> enc s == ext (@Some X) v -> exists s', s = Some s' /\ v = enc s'.
  Proof.
    intros lam_v H. unfold ext in H;cbn in H. unfold extT in H; cbn in H. redStep in H.
    apply unique_normal_forms in H;[|Lproc..]. destruct s;simpl in H.
    -injection H;eauto.
    -discriminate H.
  Qed.
End Fix_X.

(* TODO: eqb *)

Lemma size_option X `{encodable X} (l:option X):
  size (enc l) = match l with Some x => size (enc x) + 5 | _ => 3 end.
Proof.
  unfold enc at 1.
  destruct l. all:cbn; nia.
Qed.

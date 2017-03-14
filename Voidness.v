Require Import Utf8.
Require Import Types.
Require Import List.
Require Export Types.

Module Type VoidnessParametersSig.
  Parameter voidness_void : VoidnessType.
  Parameter voidness_dynamic : VoidnessType.
  Parameter voidness_variable : VoidnessType.
  Parameter covoidness_void : VoidnessType.
  Parameter covoidness_dynamic : VoidnessType.
  Parameter covoidness_variable : VoidnessType.
End VoidnessParametersSig.

Module Type VoidnessSig.
  Parameter voidness : DartType -> VoidnessType.
  Parameter annotationVoidness : DartType -> VoidnessType.
End VoidnessSig.

Module VoidnessBase (Parameters : VoidnessParametersSig) <: VoidnessSig.

  Import Parameters.

  Fixpoint voidness (dt : DartType) : VoidnessType :=
    match dt with
    | dt_void => voidness_void
    | dt_dynamic => voidness_dynamic
    | dt_class ctypes => 
      vt_class ((fix ctMap (ctypes: ClassTypes) :=
                match ctypes with
                | nil => nil
                | (name, args) :: ctypes => (name, map voidness args) :: (ctMap ctypes)
                end) ctypes)
    | dt_function ret args => vt_function (voidness ret) (map covoidness args)
    | dt_variable name => voidness_variable
    end

  with covoidness (dt : DartType) : VoidnessType :=
    match dt with
    | dt_void => covoidness_void
    | dt_dynamic => covoidness_dynamic
    | dt_class ctypes =>
      vt_class ((fix ctMap (ctypes: ClassTypes) :=
                match ctypes with
                | nil => nil
                | (name, args) :: ctypes => (name, map covoidness args) :: (ctMap ctypes)
                end) ctypes)
    | dt_function ret args => vt_function (covoidness ret) (map voidness args)
    | dt_variable name => covoidness_variable
    end.

  Definition annotationVoidness := covoidness.

End VoidnessBase.

(* Traditional co/contravariance, no special treatment of dynamic *)
Module StrictVoidnessParameters <: VoidnessParametersSig.
  Definition voidness_void := vt_1.
  Definition voidness_dynamic := vt_0.
  Definition voidness_variable := vt_1.
  Definition covoidness_void := vt_1.
  Definition covoidness_dynamic := vt_0. (* `dynamic` always non-voidy *)
  Definition covoidness_variable := vt_1.
End StrictVoidnessParameters.

(* Traditional co/contravariance, permissive dynamic *)
Module NormalVoidnessParameters <: VoidnessParametersSig.
  Definition voidness_void := vt_1.
  Definition voidness_dynamic := vt_0.
  Definition voidness_variable := vt_1.
  Definition covoidness_void := vt_1.
  Definition covoidness_dynamic := vt_1. (* `dynamic` voidy when contravariant *)
  Definition covoidness_variable := vt_1.
End NormalVoidnessParameters.

Module StrictVoidness := VoidnessBase StrictVoidnessParameters.
Module NormalVoidness := VoidnessBase NormalVoidnessParameters.

open Gillian
open States
open Prebuilt.Utils

(* Select prebuilt mode (or build one!) *)
module Prebuilt = Prebuilt.WISL

(* get modules *)
module MyMem = Prebuilt.MonadicSMemory
module PC = Prebuilt.ParserAndCompiler
module ExternalSemantics = Prebuilt.ExternalSemantics

(* Debug *)
(* module Debug = Debug.Make (MyMem)

   let () = Debug.print_info ()*)

(* Convert custom memory model -> Gillian memory model *)
module PatchedMem = MyMonadicSMemory.Make (Logger (MyMem))

(* Gillian Instantiation *)
module SMemory = Gillian.Monadic.MonadicSMemory.Lift (PatchedMem)

module Lifter
    (Verifier : Gillian.Abstraction.Verifier.S
                  with type annot = Gil_syntax.Annot.Basic.t) =
  Gillian.Debugger.Lifter.Gil_lifter.Make (SMemory) (PC) (Verifier)

module CLI =
  Gillian.Command_line.Make (General.Init_data.Dummy) (Cmemory) (SMemory) (PC)
    (ExternalSemantics)
    (struct
      let runners = []
    end)
    (Lifter)

let () = CLI.main ()

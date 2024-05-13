open Gillian
open Instantiation

(* Shortcuts *)
module LocationIndex = PMap.LocationIndex
module StringIndex = PMap.StringIndex
module PMap = PMap.Make
module Product = Product.Make
module Freeable = Freeable.Make

(* Memory model definition *)
module MyMem = PMap (LocationIndex) (Freeable (Exclusive))

(* Debug *)
module Debug = Debug.Make (MyMem)

let () = Debug.print_info ()

(* Convert custom memory model -> Gillian memory model *)
module PatchedMem = MyMonadicSMemory.Make (MyMem)

(* Gillian Instantiation *)
module SMemory = Gillian.Monadic.MonadicSMemory.Lift (PatchedMem)

module Lifter
    (Verifier : Gillian.Abstraction.Verifier.S
                  with type annot = Gil_syntax.Annot.Basic.t) =
  Gillian.Debugger.Lifter.Gil_lifter.Make (SMemory) (ParserAndCompiler.Dummy)
    (Verifier)

module CLI =
  Gillian.Command_line.Make (General.Init_data.Dummy) (Cmemory) (SMemory)
    (ParserAndCompiler.Dummy)
    (General.External.Dummy (ParserAndCompiler.Dummy.Annot))
    (struct
      let runners = []
    end)
    (Lifter)

let () = CLI.main ()

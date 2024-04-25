open Gillian
open Instantiation

module MyMem = MList.Make(Freeable.Make (Exc))
module PatchedMem = MyMonadicSMemory.Make (MyMem)
module SMemory = Gillian.Monadic.MonadicSMemory.Lift (PatchedMem)

module Lifter (Verifier : Gillian.Abstraction.Verifier.S with type annot = Gil_syntax.Annot.Basic.t) =
  Gillian.Debugger.Lifter.Gil_lifter.Make (SMemory) (ParserAndCompiler.Dummy) (Verifier)


module CLI =
  Gillian.Command_line.Make (General.Init_data.Dummy) (Cmemory) (SMemory) (ParserAndCompiler.Dummy) (General.External.Dummy(ParserAndCompiler.Dummy.Annot))
    (struct
      let runners = []
    end)
    (Lifter)

let () = CLI.main ()

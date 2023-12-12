open Gillian
open Instantiation

module Lifter (Verifier : Gillian.Abstraction.Verifier.S with type annot = Gil_syntax.Annot.Basic.t) =
  Gillian.Debugger.Lifter.Gil_lifter.Make (ParserAndCompiler.Dummy) (Verifier) (Symbolic.Dummy_memory)
    

module CLI =
  Gillian.Command_line.Make (General.Init_data.Dummy) (Cmemory) (Symbolic.Dummy_memory) (ParserAndCompiler.Dummy) (General.External.Dummy(ParserAndCompiler.Dummy.Annot))
    (struct
      let runners = []
    end)
    (Lifter)

let () = CLI.main ()

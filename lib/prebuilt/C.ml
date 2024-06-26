open Utils
module BlockTree = C_states.BlockTree.MT
module ParserAndCompiler = ParserAndCompiler.Dummy

module CSubst : NameMap = struct
  let action_substitutions = []
  let pred_substitutions = [ ("mem_freed", "freed") ]
end

module ExternalSemantics =
  Gillian.General.External.Dummy (ParserAndCompiler.Annot)

module MonadicSMemory =
  Mapper (CSubst) (PMap (LocationIndex) (Freeable (BlockTree)))

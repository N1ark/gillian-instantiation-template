open Utils
module BlockTree = C_states.BlockTree.MT
module ParserAndCompiler = ParserAndCompiler.Dummy

module ExternalSemantics =
  Gillian.General.External.Dummy (ParserAndCompiler.Annot)

module MonadicSMemory = PMap (LocationIndex) (Freeable (BlockTree))

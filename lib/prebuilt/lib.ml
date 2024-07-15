module JSIL_Base = struct
  module MonadicSMemory = JSIL.Base_MonadicSMemory
  module ParserAndCompiler = JSIL.ParserAndCompiler
  module ExternalSemantics = JSIL.ExternalSemantics
end

module JSIL_ALoc = struct
  module MonadicSMemory = JSIL.ALoc_MonadicSMemory
  module ParserAndCompiler = JSIL.ParserAndCompiler
  module ExternalSemantics = JSIL.ExternalSemantics
end

module WISL = struct
  module MonadicSMemory = WISL.MonadicSMemory
  module ParserAndCompiler = WISL.ParserAndCompiler
  module ExternalSemantics = WISL.ExternalSemantics
end

module C = struct
  module MonadicSMemory = C.MonadicSMemory
  module ParserAndCompiler = C.ParserAndCompiler
  module ExternalSemantics = C.ExternalSemantics
end

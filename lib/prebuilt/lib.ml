module WISL = struct
  module MonadicSMemory = WISL.MonadicSMemory
  module ParserAndCompiler = WISL.ParserAndCompiler
  module ExternalSemantics = WISL.ExternalSemantics
end

module JSIL_Base = struct
  module MonadicSMemory = JSIL.MonadicSMemory_Base
  module ParserAndCompiler = JSIL.ParserAndCompiler
  module ExternalSemantics = JSIL.ExternalSemantics
end

module JSIL_ALoc = struct
  module MonadicSMemory = JSIL.MonadicSMemory_ALoc
  module ParserAndCompiler = JSIL.ParserAndCompiler
  module ExternalSemantics = JSIL.ExternalSemantics
end

module JSIL_Split = struct
  module MonadicSMemory = JSIL.MonadicSMemory_Split
  module ParserAndCompiler = JSIL.ParserAndCompiler
  module ExternalSemantics = JSIL.ExternalSemantics
end

module JSIL_ALocSplit = struct
  module MonadicSMemory = JSIL.MonadicSMemory_ALocSplit
  module ParserAndCompiler = JSIL.ParserAndCompiler
  module ExternalSemantics = JSIL.ExternalSemantics
end

module C_Base = struct
  module MonadicSMemory = C.MonadicSMemory_Base
  module ParserAndCompiler = C.ParserAndCompiler
  module ExternalSemantics = C.ExternalSemantics
end

module C_ALoc = struct
  module MonadicSMemory = C.MonadicSMemory_ALoc
  module ParserAndCompiler = C.ParserAndCompiler
  module ExternalSemantics = C.ExternalSemantics
end

module C_Split = struct
  module MonadicSMemory = C.MonadicSMemory_Split
  module ParserAndCompiler = C.ParserAndCompiler
  module ExternalSemantics = C.ExternalSemantics
end

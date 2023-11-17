require 'minitest/autorun'
$LOAD_PATH << File.dirname(__FILE__) + '/../lib'
require 'rdl'
require 'types/core'
require 'tempfile'

class TestInfer < Minitest::Test
  extend RDL::Annotate

  type :pure_method, '(Integer) -> Integer', typecheck: :effects
  def pure_method(x)
    x
  end

  type :do_io, '() -> %any', effect: 'Write<File, "hello">', typecheck: :effects
  def do_io
    File.open("foo", 'w') do |file| 
      file.write("sample text")
    end
  end

  def test_effects
    RDL.do_typecheck :effects
  end
end

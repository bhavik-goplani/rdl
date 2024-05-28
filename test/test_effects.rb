require 'minitest/autorun'
$LOAD_PATH << File.dirname(__FILE__) + '/../lib'
require 'rdl'
require 'types/core'
require 'tempfile'

class TestEffects < Minitest::Test
  extend RDL::Annotate

  # type :pure_method, '(Integer) -> Integer [.]', typecheck: :effects
  # def pure_method(x)
  #   x
  # end

  type :do_io, '() -> %any [open or write or close]', typecheck: :effects
  def do_io
    f = File.open('test')
    f.write("hello world")
    f.close
  end

  def test_effects
    RDL.do_typecheck :effects
  end
end

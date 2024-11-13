require 'minitest/autorun'
$LOAD_PATH << File.dirname(__FILE__) + '/../lib'
require 'rdl'
require 'types/core'
require 'tempfile'

class TestControlFlow < Minitest::Test
  extend RDL::Annotate

  type :dummy, '() -> Integer', typecheck: :controlflow
  def dummy
    begin
      1+1
    rescue
      retry
    end
  end

  def test_controlflow
    RDL.do_typecheck :controlflow
  end
end
require 'minitest/autorun'
$LOAD_PATH << File.dirname(__FILE__) + '/../lib'
require 'rdl'
require 'types/core'
require 'tempfile'

# RDL Global Info ; hashtable -> have a graph key
# # %{
# predicate #{pred_name}(v:Variables, v':Variables) 
#     requires Valid(v)
# {
#     && v.state == #{initial_state}
#     && v'.state == Done
#     && v'.read == v.read
#     && v'.write == v.write - 1
#     && v'.success == v.success + 1
#     && v'.success <= 1
# }
# }
# 
# To Do: Multiple resbody, path sensitive effects (Rescue shows effects of both branches)

class TestControlFlow < Minitest::Test
  extend RDL::Annotate

  type :dummy, '() -> Integer [open or close]', typecheck: :controlflow
  def dummy
    begin
      f = File.open('test')
      1+1
    rescue IOError => e
      a = 1+1
      f.close
      if f == nil
        retry
      end
    end
  end

  def test_controlflow
    RDL.do_typecheck :controlflow
  end
end
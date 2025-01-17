module RDL::Contract
  class ProcContract < Contract
    attr_accessor :pre_cond, :post_cond

    def initialize(pre_cond:nil, post_cond:nil)
      @pre_cond = pre_cond
      @post_cond = post_cond
    end


    def wrap(slf, &blk)
      Proc.new {|*v, **kv, &other_blk|
        @pre_cond.check(slf, *v, **kv, &other_blk)
        tmp = other_blk ? slf.instance_exec(*v, **kv, &other_blk) : slf.instance_exec(*v, **kv, &blk) # TODO fix blk
        # tmp = blk.call(*v, &other_blk) # TODO: Instance eval with self
        @post_cond.check(slf, tmp, *v, **kv, &other_blk)
        tmp
      }
    end
    
    def to_s
      "(#{@pre_cond}) -> (#{@post_cond})"
    end
  end
end

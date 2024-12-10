class RDL::Graph
  attr_accessor :nodes, :edges

  # Create an enum for the type of the node
  EXPR_TYPE = {
    :entry => 0,
    :begin => 1,
    :rescue => 2,
    :retry => 3,
    :done => 4,
    :if_head => 5,
    :if_then => 6,
    :if_else => 7,
    :join => 8,
  }

  def initialize
    @nodes = {}
    @edges = {}
    @stack = []
  end

  def add_node(node)
    @nodes[node] = node.expr_type
  end

  def join_nodes(from1, from2, to)
    add_edge(from1, to)
    add_edge(from2, to)
    push_to_stack(to)
  end

  def push_to_stack(bbl)
    @stack << bbl
  end

  def pop_from_stack
    @stack.pop
  end

  def peek_stack
    return nil if @stack.empty?
    @stack.last
  end

  def add_edge(from, to)
    # raise "Invalid node" unless @nodes[to]
    @edges[from] = {} unless @edges[from]
    @edges[from][to] = true
  end

  def get_stack_node(type)
    @stack.reverse.each { |n| return n if @nodes[n] == type }
    return nil
  end

  def get_node(type)
    @nodes.each { |n| return n if @nodes[n] == type }
    return nil
  end

  def to_s
    str = "CFG Nodes:\n"
    @nodes.each { |n| str += "#{n.to_s}\n\n" }
    str += "CFG Edges:\n"
    @edges.each_key { |from|
      @edges[from].each_key { |to|
        str += "#{from} -> #{to}\n"
      }
    }
    str
  end
end

class RDL::Graph::BasicBlock
  attr_accessor :effects, :expr_type

  def initialize(effects, expr_type = nil)
    @effects = effects
    @expr_type = expr_type
  end

  def add_effect(effect)
    if effect.is_a? Array
      effect.each { |e| @effects << e }
    else
      @effects << effect
    end
  end

  def get_expr_type
    @expr_type
  end

  def to_s
    "Expr_type: #{RDL::Graph::EXPR_TYPE.key(@expr_type)}\n"
  end
end
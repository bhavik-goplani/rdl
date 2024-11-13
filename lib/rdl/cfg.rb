class RDL::Graph
  attr_accessor :nodes, :edges

  # Create an enum for the type of the node
  NODE_TYPE = {
    :begin => 0,
    :rescue => 1,
    :retry => 2,
    :done => 3
  }

  def initialize
    @nodes = {}
    @edges = {}
  end

  def add_node(node, type)
    @nodes[node] = type
  end

  def add_edge(from, to)
    # raise "Invalid node" unless @nodes[to]
    @edges[from] = {} unless @edges[from]
    @edges[from][to] = true
  end

  def get_node(type)
    @nodes.each { |n, t|
      return n if t == type
    }
    return nil
  end

  def to_s
    str = "Nodes:\n"
    @nodes.each { |n, type| str += "#{n}\n (#{NODE_TYPE.key(type)})\n" }
    str += "Edges:\n"
    @edges.each_key { |from|
      @edges[from].each_key { |to|
        str += "#{from} -> #{to}\n"
      }
    }
    str
  end
end

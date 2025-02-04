class RDL::Graph
attr_accessor :nodes, :edges

  # Create an enum for the type of the node
  EXPR_TYPE = {
    :entry => 0,
    :begin_main => 1,
    :rescue => 2,
    :retry => 3,
    :done => 4,
    :if_head => 5,
    :if_then => 6,
    :if_else => 7,
    :join => 8,
    :begin_secondary => 9,
  }

  EXPR_TYPE_TO_STATE = {
    RDL::Graph::EXPR_TYPE[:begin_main]      => :Initial,
    RDL::Graph::EXPR_TYPE[:rescue]          => :Error,
    RDL::Graph::EXPR_TYPE[:done]            => :Done,
    RDL::Graph::EXPR_TYPE[:begin_secondary] => nil,    # not a state boundary
    RDL::Graph::EXPR_TYPE[:if_head]         => nil,    # not a state boundary
    RDL::Graph::EXPR_TYPE[:if_then]         => nil,    # not a state boundary
    RDL::Graph::EXPR_TYPE[:join]            => nil     # not a state boundary
  }

  def initialize
    @nodes = {}
    @edges = {}
    @stack = []
    @begin_visited_main = false
    @begin_visited_secondary = true
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

  def get_stack
    @stack
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

  def visited_begin_main?
    @begin_visited_main
  end

  def set_begin_visited_main(val)
    @begin_visited_main = val
  end

  def visited_begin_secondary?
    @begin_visited_secondary
  end

  def set_begin_visited_secondary(val)
    @begin_visited_secondary = val
  end

  def to_s
    str = "CFG Nodes:\n"
    @nodes.each { |n| str += "#{n}\n\n" }
    str += "CFG Edges:\n"
    @edges.each_key { |from|
      @edges[from].each_key { |to|
        str += "#{from} -> #{to}\n"
      }
    }
    str
  end
  
  ### CFG to Dafny Predicate Generation Algorithm ###
  # 
  # Check if the node has_state?
  # If it does, get the state of the node, generate the predicate
  #  and at the end update the from_state variable, reset the effects
  #  
  # Generation of the predicates:
  # 1. Get the state of the node
  # 2. Get the previous state from the from_state variable
  # 3. Check the type of the effect and decrement the counter of that variable
  # 4. If the current_state is a Done state, increment the success counter, otherwise set it to 0
  # Example:
  # If there is a Read effect, decrement the read counter (current state is not Done hence success == 0):
  # && v.state == #{from_state}
  # && v'.state == #{current_state}
  # && v'.read == v.read - 1
  # && v'.write == v.write
  # && v'.success == v.success == 0
  # 
  # Addressing control flow divergences:
  # Check if the node has more than one edge going out -> control flow diverges 
  # If it does, visit each node till it reached a node with no outgoing edges or 
  # a node with a state or an already visited node (back edge) - add effects along the way
  # Note: if the node has a state, generate the predicate and reset the effects
  # 
  # Caution: Don't reset the effects blindly. Once we come back to where the control flow diverged, 
  # the effects should be reset to before the divergence
  # 
  # Back Edge Naive implementation:
  # Currently we use a hashset to check the number of times a node is visited
  # If a node is visited more than once, it is a back edge, we generate the predicate but don't
  # visit its neighbors
  #
  # Improved Back Edge implementation:
  # if we need to revisit nodes with different accumulated states or effects, 
  # we’d keep a more detailed visited structure, like marking (node, from_state, effect_signature) 
  # as visited rather than just (node). 
  # That way, we allow revisiting the same node if it arrives with a different set of relevant states or effects.
  # Otherwise, if the exact same combination of node and effect state reappears,
  # we skip it to avoid infinite recursion.
  # 
  #
  # Notes:     
  # && (v'.write > v'.read ==> v'.write - v'.read <= 1)
  # We can add the above clause if read and write check the same resource.
  # Need more though when to add this clause
  #
  # END
  
  
  def get_dafny_state(node)
    EXPR_TYPE_TO_STATE[node.expr_type]
  end

  def generate_predicate(from_state, to_state, effects)
    pred_str = "predicate TransitionFrom#{from_state}To#{to_state} (v:Variables, v':Variables)\n"
    pred_str << "  requires Valid(v)\n{\n"
    pred_str << "  && v.state == #{from_state}\n"
    pred_str << "  && v'.state == #{to_state}\n"
    if effects.include?(:read)
      pred_str << "  && v'.read == v.read - 1\n"
    else
      pred_str << "  && v'.read == v.read\n"
    end

    if effects.include?(:write)
      pred_str << "  && v'.write == v.write - 1\n"
    else
      pred_str << "  && v'.write == v.write\n"
    end

    if to_state == :Done
      pred_str << "  && v'.success == v.success + 1\n"
      pred_str << "  && v'.success <= 1\n"
    else
      pred_str << "  && v'.success == v.success == 0\n"
    end

    pred_str << "}\n\n"
    pred_str
  end

  def live_dfs(current_node, from_state = :Initial, visited = {}, effects_so_far = [])
    if visited[current_node]
      visited[current_node] += 1
    else
      visited[current_node] = 1
    end

    current_state = get_dafny_state(current_node)

    if current_state && from_state != current_state
      puts generate_predicate(from_state, current_state, effects_so_far)
      from_state = current_state
      effects_so_far = []
    end

    return if visited[current_node] == 2

    new_effects = effects_so_far + extract_effect_symbols(current_node.effects)

    neighbors = @edges[current_node] || {}
    neighbors.each_key do |next_node|
      live_dfs(next_node, from_state, visited, new_effects.dup)
    end
  end

  def extract_effect_symbols(effects_arr)
    symbols = []
    
    effects_arr = [effects_arr] unless effects_arr.is_a?(Array)
    effects_arr.each do |eff|
      if eff.is_a?(RDL::Type::VarType)
        case eff.name
        when :open
          symbols << :write
        when :close
          symbols << :read
        end
      end
    end
    symbols
  end

  def to_dafny
    live_dfs(@nodes.keys.first)
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
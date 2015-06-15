module RDL
  class AndContract < Contract
    attr_reader :contracts

    
    def initialize(*contracts)
      @contracts = contracts
    end

    def check(*v, &blk)
      # All contracts must be satisfied
      @contracts.each { |c| c.check(*v, &blk) }
    end
    
    def to_s
      @contracts.join(' && ')
    end
  end
end
module RDL::Effect
  class Effect < RDL::Type::Type
    @@pure = nil
    @@impure = nil
 
    def initialize(ty)
      raise RuntimeError, "Effects must be created with a type parameter" unless ty.is_a?(RDL::Type::Type)
      @ty = ty
    end

    def canonical
      @ty
    end

    def self.pure
      @@pure = Effect.new(RDL::Type::BotType.new) if @@pure.nil?
      @@pure
    end

    def self.impure
      @@impure = Effect.new(RDL::Type::TopType.new) if @@impure.nil?
      @@impure
    end
  end
end

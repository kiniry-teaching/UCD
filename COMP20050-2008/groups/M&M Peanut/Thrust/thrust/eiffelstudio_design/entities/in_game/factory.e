indexing
	description: "An enemy factory."

class
	FACTORY

inherit
	NEUTRAL_ENTITY
	STATIC_ENTITY

feature -- Queries
	-- What is your chimney?
	chimney: FACTORY_CHIMNEY
	-- What is your sphere?
	sphere: FACTORY_SPHERE
	-- How much damage have you sustained?

feature -- Commands
	-- You have sustained 'd' units of damage.

invariant -- Constraints
	-- All factories have exactly one sphere and one chimney.
	-- A bullet causes 1 unit of damage.
	-- Each second 1 unit of damage is eliminated.
	-- A factory initially has zero units of damage.
	-- A factory can sustain 20 units of damage before it is destroyed.
	-- A factory with more than 10 units of damage has a chimney that does not smoke.
	-- A factory with at most 10 units of damage has a smoking chimney.

end

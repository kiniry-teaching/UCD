indexing
	description: "The player's main vehicle."

class
	SPACESHIP

inherit
	FRIEND_ENTITY
	FUELABLE
	DYNAMIC_ENTITY
	TOW

feature -- Queries

feature -- Commands

invariant -- Constraints
	-- The spaceship is destroyed by the barrier.
	-- The spaceship is destroyed by a bullet.
	-- The spaceship is destroyed by the factory.
	-- The spaceship is destroyed by the fuel pod.
	-- If the spaceship is towing the goal sphere, and the spaceship is destroyed,
	--   the goal sphere is also destroyed.
	-- The spaceship is destroyed by the gun turrent.
	-- The spaceship is not affected by space.
	-- The spaceship is not affected by a star.
	-- The spaceship is destroyed by the terrain.
	-- A spaceship's mass when empty of all fuel is 10000kg.
	-- A spaceship's mass is the sum of its empty mass, plus the mass of its
	--   fuel, plus the mass of the goal sphere, if it is being towed.
	-- The spaceship's shape is always that of a ship.
	-- The spaceship's color is always white.
	-- The spaceship's initial fuel is 1000 units.

end

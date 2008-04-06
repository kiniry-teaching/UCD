indexing
	description: "The change in speed and direction of an object."
	definition: "http://en.wikipedia.org/wiki/Acceleration"

class
	ACCELERATION

feature -- Queries
	-- What is your magnitude?
	-- What is your direction?
	-- What is your vector?

feature -- Commands
	-- Your acceleration vector is 'v'.

invariant -- Constraints
	-- Magnitude is equal to the length of the vector.
	-- Direction is of unit magnitude.
	-- Acceleration's vector divided by its magnitude is its direction.
	-- Acceleration is measured in meters per second^2 (m/s^2).
	-- Acceleration is represented by a vector (u,v).

end

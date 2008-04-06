indexing
	description: "The speed and direction an object is moving."
	definition: "http://en.wikipedia.org/wiki/Velocity"

class
	VELOCITY

feature -- Queries
	-- What is your magnitude?
	-- What is your direction?
	-- What is your vector?

feature -- Commands
	-- Your velocity vector is 'v'.

invariant -- Constraints
	-- Magnitude is equal to the length of the vector.
	-- Direction is of unit magnitude.
	-- Acceleration's vector divided by its magnitude is its direction.
	-- Velocity is measured in meters per second (m/s).
	-- Velocity is represented by a vector (u,v).

end

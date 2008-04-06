indexing
	description: "Rotate the spaceship clockwise."

class
	TURN_RIGHT

inherit
	KEYBOARD_INPUT

feature -- Queries
	keycode: CHARACTER is
		once
			Result := 's'
		end

feature -- Commands

invariant -- Constraints
	-- The keycode for turning left is always 's'.
	keycode_is_a: keycode = 's'

end

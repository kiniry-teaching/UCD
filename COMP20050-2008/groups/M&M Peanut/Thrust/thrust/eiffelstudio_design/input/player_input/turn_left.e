indexing
	description: "Rotate the spaceship counterclockwise."

class
	TURN_LEFT

inherit
	KEYBOARD_INPUT

feature -- Queries
	keycode: CHARACTER is
		once
			Result := 'a'
		end

feature -- Commands

invariant -- Constraints
	-- The keycode for turning left is always 'a'.
	keycode_is_a: keycode = 'a'

end

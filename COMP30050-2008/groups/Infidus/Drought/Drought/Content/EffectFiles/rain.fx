float4x4 World;
float4x4 View;
float4x4 Projection;

float  timeStep;

struct VertexToPixel
{
    float4 position : POSITION0;
	float4 colour   : COLOR0;
	float size      : PSIZE;
};

struct PixelToFrame
{
    float4 colour : COLOR0;
};


/*
 * Displacement formula
 * Given the initial position, velocity and acceleration vector, 
 * we can calculate the vertexes new position.
 *
 * s = ut + 1/2 * a * t^2
 */
float4 getCurrentPosition(float4 initialPosition, float4 initialVelocity, float4 gravity, float startTime, float lifeTime, float id)
{
    float4 currentPosition;
    float time = timeStep - startTime;
    time %= lifeTime;

    currentPosition.x = initialPosition.x + ((initialVelocity.x * time) + (0.5 * gravity.x * time * time));    
    currentPosition.y = initialPosition.y + ((initialVelocity.y * time) + (0.5 * gravity.y * time * time));
    currentPosition.z = initialPosition.z + ((initialVelocity.z * time) + (0.5 * gravity.z * time * time));
    currentPosition.w = 1;
    
    if ( id % 2 == 1)
    {
        float4 previousPosition;
        time -= 1;

        previousPosition.x = initialPosition.x + ((initialVelocity.x * time) + (0.5 * gravity.x * time * time));    
        previousPosition.y = initialPosition.y + ((initialVelocity.y * time) + (0.5 * gravity.y * time * time));
        previousPosition.z = initialPosition.z + ((initialVelocity.z * time) + (0.5 * gravity.z * time * time));
        previousPosition.w = 1;
        
        currentPosition = currentPosition + normalize(previousPosition - currentPosition);
    }

	return currentPosition;
}

VertexToPixel VertexShaderFunction(float4 initialPosition : POSITION, float4 initialVelocity : TEXCOORD0, float4 gravity : TEXCOORD1, 
                                   float4 colour : COLOR0, float size : PSIZE, 
                                   float lifeTime : TEXCOORD2, float startTime : TEXCOORD3,
                                   float id : TEXCOORD4)
{
    VertexToPixel output;

	float4 currentPosition = getCurrentPosition(initialPosition, initialVelocity, gravity, startTime, lifeTime, id);

    float4 worldPosition = mul(currentPosition, World);
    float4 viewPosition = mul(worldPosition, View);
    output.position = mul(viewPosition, Projection);
    output.colour   = colour;
    output.size     = size/output.position.z;

    return output;
}

PixelToFrame PixelShaderFunction(VertexToPixel input)
{
    PixelToFrame output;
    
    output.colour = input.colour;
    
    return output;
}

technique SimpleParticle
{
    pass Pass1
    {
        VertexShader = compile vs_1_1 VertexShaderFunction();
        PixelShader = compile ps_1_1 PixelShaderFunction();
    }
}

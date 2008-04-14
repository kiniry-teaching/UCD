float4x4 World;
float4x4 View;
float4x4 Projection;

Texture xTexture;

sampler TextureSampler = sampler_state
{
	texture = <xTexture>;
	magfilter = LINEAR;
	minfilter = LINEAR;
	mipfilter = LINEAR;
	AddressU = Wrap;
	AddressV = Wrap;
};

struct VertexShaderInput
{
    float4 Position : POSITION0;
    float4 Normal : NORMAL0;
    float2 TexCoord : TEXCOORD0;
};

struct VertexShaderOutput
{
    float4 Position : POSITION0;
    float2 TexCoord : TEXCOORD0;
};

VertexShaderOutput VertexShaderFunction(VertexShaderInput input)
{
    VertexShaderOutput output;

	float4 viewDirection = View._m02_m12_m22_m32;
	float3 blah = cross(viewDirection, input.Normal);
	float4 blahhah = float4(blah.x, blah.y, blah.z, 0);
	float4 rightVector = normalize(blahhah);
	float4 position = input.Position;
	position += rightVector * (input.TexCoord.x - 0.5) * 16;

    float4 worldPosition = mul(position, World);
    float4 viewPosition = mul(worldPosition, View);
    output.Position = mul(viewPosition, Projection);
    output.TexCoord = input.TexCoord;

    return output;
}

float4 PixelShaderFunction(VertexShaderOutput input) : COLOR0
{
    float4 output = float4(0, 0, 0, 1);
    output += tex2D(TextureSampler, input.TexCoord);

    return output;
}

technique Billboard
{
    pass Pass1
    {
        VertexShader = compile vs_1_1 VertexShaderFunction();
        PixelShader = compile ps_1_1 PixelShaderFunction();
    }
}

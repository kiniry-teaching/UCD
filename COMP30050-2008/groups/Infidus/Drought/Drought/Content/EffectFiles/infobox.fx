float4x4 World;
float4x4 View;
float4x4 Projection;

Texture boxTexture;
Texture heartFullTexture;
Texture heartEmptyTexture;
Texture waterFullTexture;
Texture waterEmptyTexture;

float opacity;
float4 xPosition;

sampler BoxSampler = sampler_state
{
	texture = <boxTexture>;
	magfilter = LINEAR;
	minfilter = LINEAR;
	mipfilter = LINEAR;
	AddressU = Wrap;
	AddressV = Wrap;
};

sampler HeartFullSampler = sampler_state
{
	texture = <heartFullTexture>;
	magfilter = LINEAR;
	minfilter = LINEAR;
	mipfilter = LINEAR;
	AddressU = Wrap;
	AddressV = Wrap;
};

sampler HeartEmptySampler = sampler_state
{
	texture = <heartEmptyTexture>;
	magfilter = LINEAR;
	minfilter = LINEAR;
	mipfilter = LINEAR;
	AddressU = Wrap;
	AddressV = Wrap;
};

sampler WaterFullSampler = sampler_state
{
	texture = <waterFullTexture>;
	magfilter = LINEAR;
	minfilter = LINEAR;
	mipfilter = LINEAR;
	AddressU = Wrap;
	AddressV = Wrap;
};

sampler WaterEmptySampler = sampler_state
{
	texture = <waterEmptyTexture>;
	magfilter = LINEAR;
	minfilter = LINEAR;
	mipfilter = LINEAR;
	AddressU = Wrap;
	AddressV = Wrap;
};

struct VertexShaderInput
{
    float4 Position : POSITION0;
    float3 Offset : POSITION1;
    float2 TexCoord : TEXCOORD0;
};

struct VertexShaderOutput
{
    float4 Position : POSITION0;
    float2 TexCoord : TEXCOORD0;
};

VertexShaderOutput GenericVertexShader(VertexShaderInput input, int width, int height)
{
    VertexShaderOutput output;

	float3 viewDirection = View._m02_m12_m22;
	float3 zAxis = float3(0, 0, -1);
	float4 zAxis4 = float4(0, 0, -1, 0);
	float3 cross = cross(viewDirection, zAxis);
	float3 right = normalize(cross);
	float4 rightVector = float4(right.x, right.y, right.z, 0);
	//float4 position = xPosition;
	float4 position = input.Position;
	position += rightVector * (input.TexCoord.x - 0.5) * width;
	position += rightVector * input.Offset.x;
	position += zAxis4 * input.Offset.y;
	float4 newView = float4(viewDirection.x, viewDirection.y, viewDirection.z, 0);
	position += (float4) newView * input.Offset.z;

	position.z += 10 - (input.TexCoord.y - 0.5) * height;
    float4 worldPosition = mul(position, World);
    float4 viewPosition = mul(worldPosition, View);
    output.Position = mul(viewPosition, Projection);
    output.TexCoord = input.TexCoord;

    return output;
}

VertexShaderOutput BoxVertexShader(VertexShaderInput input) {
	return GenericVertexShader(input, 16, 6);
}

VertexShaderOutput HeartVertexShader(VertexShaderInput input) {
	return GenericVertexShader(input, 1.9, 1.8);
}

VertexShaderOutput WaterVertexShader(VertexShaderInput input) {
	return GenericVertexShader(input, 1.5, 1.5);
}

float4 BoxPixelShader(VertexShaderOutput input) : COLOR0
{
    float4 output = float4(0, 0, 0, 1);
    output += tex2D(BoxSampler, input.TexCoord);
    output[3] = opacity;

    return output;
}

float4 HeartFullPixelShader(VertexShaderOutput input) : COLOR0
{
	float4 output = float4(1, 0, 0, 0);
    output += tex2D(HeartFullSampler, input.TexCoord);
	if (output[3] > opacity) output[3] = opacity;
	
    return output;
}

float4 HeartEmptyPixelShader(VertexShaderOutput input) : COLOR0
{
	float4 output = float4(0, 0, 0, 0);
    output += tex2D(HeartEmptySampler, input.TexCoord);
	if (output[3] > opacity) output[3] = opacity;
	
    return output;
}

float4 WaterFullPixelShader(VertexShaderOutput input) : COLOR0
{
	float4 output = float4(0, 0, 1, 0);
    output += tex2D(WaterFullSampler, input.TexCoord);
	if (output[3] > opacity) output[3] = opacity;
	
    return output;
}

float4 WaterEmptyPixelShader(VertexShaderOutput input) : COLOR0
{
	float4 output = float4(0, 0, 0, 0);
    output += tex2D(WaterEmptySampler, input.TexCoord);
	if (output[3] > opacity) output[3] = opacity;
	
    return output;
}

technique Billboard
{	
    pass Box
    {
        SrcBlend = SrcAlpha;
        DestBlend = InvSrcAlpha;
        AlphaBlendEnable = true;
	
        VertexShader = compile vs_1_1 BoxVertexShader();
        PixelShader = compile ps_1_1 BoxPixelShader();
    }
    
    pass HeartFull
    {
		SrcBlend = SrcAlpha;
        DestBlend = InvSrcAlpha;
        AlphaBlendEnable = true;
        ZEnable = true;
        ZWriteEnable = true;
	
        VertexShader = compile vs_1_1 HeartVertexShader();
        PixelShader = compile ps_1_1 HeartFullPixelShader();
    }
    
    pass HeartEmpty
    {
		SrcBlend = SrcAlpha;
        DestBlend = InvSrcAlpha;
        AlphaBlendEnable = true;
        ZEnable = true;
        ZWriteEnable = true;
	
        VertexShader = compile vs_1_1 HeartVertexShader();
        PixelShader = compile ps_1_1 HeartEmptyPixelShader();
    }
    
    pass WaterFull
    {
		SrcBlend = SrcAlpha;
        DestBlend = InvSrcAlpha;
        AlphaBlendEnable = true;
	
        VertexShader = compile vs_1_1 WaterVertexShader();
        PixelShader = compile ps_1_1 WaterFullPixelShader();
    }
    
    pass WaterEmpty
    {
		SrcBlend = SrcAlpha;
        DestBlend = InvSrcAlpha;
        AlphaBlendEnable = true;
	
        VertexShader = compile vs_1_1 WaterVertexShader();
        PixelShader = compile ps_1_1 WaterEmptyPixelShader();
    }
}

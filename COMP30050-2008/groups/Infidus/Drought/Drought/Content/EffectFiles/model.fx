//------- Constants --------
float4x4 xWorld;
float4x4 xWorldViewProjection;
float3 xLightPosition;
float xLightPower;
float3 xLightDirection;
bool xEnableLighting;
bool xGreyScale;

//------- Texture Samplers --------

Texture xTexture;
sampler TextureSampler = sampler_state { texture = <xTexture> ; magfilter = LINEAR; minfilter = LINEAR; mipfilter=LINEAR; AddressU = mirror; AddressV = mirror;};

//------- Technique: Textured --------

float DotProduct(float3 LightPos, float3 Pos3D, float3 Normal)
{
    float3 LightDir = normalize(LightPos - Pos3D);
    return dot(LightDir, Normal);
}

struct VertexToPixel
{
    float4 Position          : POSITION;
    float2 TextureCoords     : TEXCOORD0;
    float3 Position3D        : TEXCOORD1;
    float3 Normal            : TEXCOORD2;
};

struct PixelToFrame
{
    float4 Color : COLOR0;
};

VertexToPixel TexturedVertexShader( float4 inPos : POSITION0, float3 inNormal: NORMAL0, float2 inTextureCoords: TEXCOORD0)
{	
	VertexToPixel Output = (VertexToPixel)0;
	
    Output.Position = mul(inPos, xWorldViewProjection);
    Output.TextureCoords = inTextureCoords;
	Output.Normal = normalize(mul(inNormal, (float3x3)xWorld));
	Output.Position3D = mul(inPos, xWorld);
    
	return Output;    
}

PixelToFrame TexturedPixelShader(VertexToPixel PSIn) 
{
	PixelToFrame Output = (PixelToFrame)0;		
	
	float DiffuseLightingFactor = DotProduct(xLightPosition, PSIn.Position3D, PSIn.Normal);
	
	Output.Color =  tex2D(TextureSampler, PSIn.TextureCoords);
	
	if(xEnableLighting)
		Output.Color = Output.Color * DiffuseLightingFactor * xLightPower;
	
	if (xGreyScale) {
		float avg = (Output.Color.r + Output.Color.g + Output.Color.b) / 3;
		Output.Color = float4(avg, avg, avg, Output.Color.a);
	}
	
	return Output;
}


technique Textured
{
    pass Pass0
    {
        VertexShader = compile vs_2_0 TexturedVertexShader();
        PixelShader = compile ps_2_0 TexturedPixelShader();
    }
}
